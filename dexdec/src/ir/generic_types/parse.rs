use crate::ir::ty::PrimitiveType;

use super::{
    ClassSignature, ClassTypeSignature, InnerClassTypeSignature, JvmTypeSignature, MethodSignature,
    SignatureError, TypeArgument, TypeParameter,
};

const MAX_DEPTH: usize = 256;

pub(super) struct Parser<'a> {
    signature: &'a str,
    bytes: &'a [u8],
    position: usize,
    depth: usize,
}

impl<'a> Parser<'a> {
    pub(super) fn new(signature: &'a str) -> Self {
        Self {
            signature,
            bytes: signature.as_bytes(),
            position: 0,
            depth: 0,
        }
    }

    pub(super) fn expect_end(&self) -> Result<(), SignatureError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(self.error())
        }
    }

    pub(super) fn class_signature(&mut self) -> Result<ClassSignature, SignatureError> {
        let type_parameters = self.optional_type_parameters()?;
        let super_class = self.class_type()?;
        let mut super_interfaces = Vec::new();
        while self.peek().is_some() {
            super_interfaces.push(self.class_type()?);
        }
        Ok(ClassSignature {
            type_parameters,
            super_class,
            super_interfaces,
        })
    }

    pub(super) fn method_signature(&mut self) -> Result<MethodSignature, SignatureError> {
        let type_parameters = self.optional_type_parameters()?;
        self.expect(b'(')?;
        let mut parameter_types = Vec::new();
        while self.peek() != Some(b')') {
            if self.peek().is_none() {
                return Err(self.error());
            }
            parameter_types.push(self.java_type()?);
        }
        self.expect(b')')?;
        let return_type = if self.eat(b'V') {
            JvmTypeSignature::BaseType(PrimitiveType::Void)
        } else {
            self.java_type()?
        };
        let mut throws = Vec::new();
        while self.eat(b'^') {
            let exception = self.reference_type()?;
            if !matches!(
                exception,
                JvmTypeSignature::ClassType(_) | JvmTypeSignature::TypeVariable(_)
            ) {
                return Err(self.error());
            }
            throws.push(exception);
        }
        Ok(MethodSignature {
            type_parameters,
            parameter_types,
            return_type,
            throws,
        })
    }

    pub(super) fn field_signature(&mut self) -> Result<JvmTypeSignature, SignatureError> {
        if self.peek() == Some(b'T') {
            return self.type_variable(true);
        }
        self.reference_type()
    }

    fn optional_type_parameters(&mut self) -> Result<Vec<TypeParameter>, SignatureError> {
        if !self.eat(b'<') {
            return Ok(Vec::new());
        }
        let mut parameters = Vec::new();
        while self.peek() != Some(b'>') {
            if self.peek().is_none() {
                return Err(self.error());
            }
            parameters.push(self.type_parameter()?);
        }
        if parameters.is_empty() {
            return Err(self.error());
        }
        self.expect(b'>')?;
        Ok(parameters)
    }

    fn type_parameter(&mut self) -> Result<TypeParameter, SignatureError> {
        let name = self.name_until(&[b':'])?;
        self.expect(b':')?;
        let class_bound = if Self::starts_reference(self.peek()) {
            Some(self.reference_type()?)
        } else {
            None
        };
        let mut interface_bounds = Vec::new();
        while self.eat(b':') {
            interface_bounds.push(self.reference_type()?);
        }
        Ok(TypeParameter {
            name,
            class_bound,
            interface_bounds,
        })
    }

    fn java_type(&mut self) -> Result<JvmTypeSignature, SignatureError> {
        if Self::starts_reference(self.peek()) {
            return self.reference_type();
        }
        let primitive = match self.peek() {
            Some(b'B') => PrimitiveType::Byte,
            Some(b'C') => PrimitiveType::Char,
            Some(b'D') => PrimitiveType::Double,
            Some(b'F') => PrimitiveType::Float,
            Some(b'I') => PrimitiveType::Int,
            Some(b'J') => PrimitiveType::Long,
            Some(b'S') => PrimitiveType::Short,
            Some(b'Z') => PrimitiveType::Boolean,
            _ => return Err(self.error()),
        };
        self.position += 1;
        Ok(JvmTypeSignature::BaseType(primitive))
    }

    fn reference_type(&mut self) -> Result<JvmTypeSignature, SignatureError> {
        if self.depth >= MAX_DEPTH {
            return Err(self.error());
        }
        self.depth += 1;
        let result = self.reference_type_inner();
        self.depth -= 1;
        result
    }

    fn reference_type_inner(&mut self) -> Result<JvmTypeSignature, SignatureError> {
        match self.peek() {
            Some(b'L') => self.class_type().map(JvmTypeSignature::ClassType),
            Some(b'T') => self.type_variable(false),
            Some(b'[') => {
                self.position += 1;
                Ok(JvmTypeSignature::Array(Box::new(self.java_type()?)))
            }
            _ => Err(self.error()),
        }
    }

    fn type_variable(
        &mut self,
        allow_end_terminator: bool,
    ) -> Result<JvmTypeSignature, SignatureError> {
        self.expect(b'T')?;
        let start = self.position;
        while self.peek().is_some_and(|byte| byte != b';') {
            self.position += 1;
        }
        if self.position == start {
            return Err(self.error());
        }
        let name = std::str::from_utf8(&self.bytes[start..self.position])
            .map(str::to_owned)
            .map_err(|_| self.error())?;
        if !self.eat(b';') && !(allow_end_terminator && self.peek().is_none()) {
            return Err(self.error());
        }
        Ok(JvmTypeSignature::TypeVariable(name))
    }

    fn class_type(&mut self) -> Result<ClassTypeSignature, SignatureError> {
        self.expect(b'L')?;
        let raw_name = self.name_until(&[b'<', b';', b'.', b'$'])?;
        let type_arguments = self.optional_type_arguments()?;
        let mut inner_segments = Vec::new();
        while matches!(self.peek(), Some(b'.' | b'$')) {
            self.position += 1;
            let simple_name = self.name_until(&[b'<', b';', b'.', b'$'])?;
            let type_arguments = self.optional_type_arguments()?;
            inner_segments.push(InnerClassTypeSignature {
                simple_name,
                type_arguments,
            });
        }
        self.expect(b';')?;
        Ok(ClassTypeSignature {
            raw_name,
            type_arguments,
            inner_segments,
        })
    }

    fn optional_type_arguments(&mut self) -> Result<Vec<TypeArgument>, SignatureError> {
        if !self.eat(b'<') {
            return Ok(Vec::new());
        }
        let mut arguments = Vec::new();
        while self.peek() != Some(b'>') {
            if self.peek().is_none() {
                return Err(self.error());
            }
            arguments.push(self.type_argument()?);
        }
        if arguments.is_empty() {
            return Err(self.error());
        }
        self.expect(b'>')?;
        Ok(arguments)
    }

    fn type_argument(&mut self) -> Result<TypeArgument, SignatureError> {
        match self.peek() {
            Some(b'*') => {
                self.position += 1;
                Ok(TypeArgument::Unbounded)
            }
            Some(b'+') => {
                self.position += 1;
                self.reference_type().map(TypeArgument::Extends)
            }
            Some(b'-') => {
                self.position += 1;
                self.reference_type().map(TypeArgument::Super)
            }
            _ => self.reference_type().map(TypeArgument::Exact),
        }
    }

    fn name_until(&mut self, delimiters: &[u8]) -> Result<String, SignatureError> {
        let start = self.position;
        while let Some(byte) = self.peek() {
            if delimiters.contains(&byte) {
                break;
            }
            self.position += 1;
        }
        if self.position == start || self.peek().is_none() {
            return Err(self.error());
        }
        std::str::from_utf8(&self.bytes[start..self.position])
            .map(str::to_owned)
            .map_err(|_| self.error())
    }

    fn starts_reference(byte: Option<u8>) -> bool {
        matches!(byte, Some(b'L' | b'T' | b'['))
    }

    fn expect(&mut self, byte: u8) -> Result<(), SignatureError> {
        if self.eat(byte) {
            Ok(())
        } else {
            Err(self.error())
        }
    }

    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() != Some(byte) {
            return false;
        }
        self.position += 1;
        true
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.position).copied()
    }

    fn error(&self) -> SignatureError {
        SignatureError {
            offset: self.position,
            signature: self.signature.to_owned(),
        }
    }
}
