use quick_xml::escape::escape;
use quick_xml::events::{BytesStart, Event};
use quick_xml::{Reader, XmlVersion};

pub struct XmlFormatter {
    indent: &'static str,
}

impl Default for XmlFormatter {
    fn default() -> Self {
        Self { indent: "    " }
    }
}

impl XmlFormatter {
    pub fn format(&self, input: &str) -> Result<String, String> {
        let document = XmlDocument::parse(input)?;
        let mut output = String::with_capacity(input.len() + input.len() / 4);
        for node in document
            .nodes
            .iter()
            .filter(|node| !node.is_ignorable_whitespace())
        {
            self.write_node(node, 0, false, &mut output);
        }
        while output.ends_with("\n\n") {
            output.pop();
        }
        Ok(output)
    }

    fn write_node(&self, node: &XmlNode, depth: usize, inline: bool, output: &mut String) {
        match node {
            XmlNode::Element(element) => self.write_element(element, depth, inline, output),
            XmlNode::Text(text) => output.push_str(text),
            XmlNode::CData(text) => {
                output.push_str("<![CDATA[");
                output.push_str(text);
                output.push_str("]]>");
            }
            XmlNode::Declaration(value) => {
                self.write_markup("<?", value, "?>", depth, inline, output)
            }
            XmlNode::ProcessingInstruction(value) => {
                self.write_markup("<?", value, "?>", depth, inline, output)
            }
            XmlNode::DocType(value) => {
                self.write_markup("<!DOCTYPE ", value, ">", depth, inline, output)
            }
            XmlNode::Comment(value) => {
                self.write_markup("<!--", value, "-->", depth, inline, output)
            }
        }
    }

    fn write_element(&self, element: &XmlElement, depth: usize, inline: bool, output: &mut String) {
        if !inline {
            self.write_indent(depth, output);
        }

        let content_is_inline = element.has_text_content();
        self.write_opening_tag(element, depth, inline || content_is_inline, output);
        if element.self_closing {
            if !inline {
                output.push('\n');
            }
            return;
        }
        if element.children.is_empty() {
            output.push_str("</");
            output.push_str(&element.name);
            output.push('>');
            if !inline {
                output.push('\n');
            }
            return;
        }

        if content_is_inline {
            for child in &element.children {
                self.write_node(child, depth + 1, true, output);
            }
        } else {
            output.push('\n');
            for child in element
                .children
                .iter()
                .filter(|child| !child.is_ignorable_whitespace())
            {
                self.write_node(child, depth + 1, false, output);
            }
            self.write_indent(depth, output);
        }
        output.push_str("</");
        output.push_str(&element.name);
        output.push('>');
        if !inline {
            output.push('\n');
        }
    }

    fn write_opening_tag(
        &self,
        element: &XmlElement,
        depth: usize,
        force_inline: bool,
        output: &mut String,
    ) {
        output.push('<');
        output.push_str(&element.name);
        let wrap = !force_inline && element.attributes.len() > 1;
        for (index, attribute) in element.attributes.iter().enumerate() {
            if wrap {
                output.push('\n');
                self.write_indent(depth + 1, output);
            } else {
                output.push(' ');
            }
            output.push_str(&attribute.name);
            output.push_str("=\"");
            output.push_str(&attribute.value);
            output.push('"');
            if wrap && index + 1 == element.attributes.len() {
                output.push_str(if element.self_closing { " />" } else { ">" });
                return;
            }
        }
        output.push_str(if element.self_closing { " />" } else { ">" });
    }

    fn write_markup(
        &self,
        prefix: &str,
        value: &str,
        suffix: &str,
        depth: usize,
        inline: bool,
        output: &mut String,
    ) {
        if !inline {
            self.write_indent(depth, output);
        }
        output.push_str(prefix);
        output.push_str(value);
        output.push_str(suffix);
        if !inline {
            output.push('\n');
        }
    }

    fn write_indent(&self, depth: usize, output: &mut String) {
        for _ in 0..depth {
            output.push_str(self.indent);
        }
    }
}

struct XmlDocument {
    nodes: Vec<XmlNode>,
}

impl XmlDocument {
    fn parse(input: &str) -> Result<Self, String> {
        let mut reader = Reader::from_str(input);
        reader.config_mut().trim_text(false);
        let mut roots = Vec::new();
        let mut stack = Vec::<XmlElement>::new();
        let mut buffer = Vec::new();
        loop {
            match reader
                .read_event_into(&mut buffer)
                .map_err(|error| error.to_string())?
            {
                Event::Start(start) => stack.push(XmlElement::from_start(&reader, &start, false)?),
                Event::Empty(start) => {
                    let element = XmlElement::from_start(&reader, &start, true)?;
                    Self::append(&mut roots, &mut stack, XmlNode::Element(element));
                }
                Event::End(end) => {
                    let element = stack
                        .pop()
                        .ok_or_else(|| "XML end tag has no matching start tag".to_string())?;
                    if element.name.as_bytes() != end.name().as_ref() {
                        return Err("XML start and end tags do not match".to_string());
                    }
                    Self::append(&mut roots, &mut stack, XmlNode::Element(element));
                }
                Event::Text(text) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::Text(String::from_utf8_lossy(text.as_ref()).into_owned()),
                ),
                Event::CData(text) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::CData(String::from_utf8_lossy(text.as_ref()).into_owned()),
                ),
                Event::Decl(declaration) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::Declaration(
                        String::from_utf8_lossy(declaration.as_ref()).into_owned(),
                    ),
                ),
                Event::PI(instruction) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::ProcessingInstruction(
                        String::from_utf8_lossy(instruction.as_ref()).into_owned(),
                    ),
                ),
                Event::DocType(doc_type) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::DocType(String::from_utf8_lossy(doc_type.as_ref()).into_owned()),
                ),
                Event::Comment(comment) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::Comment(String::from_utf8_lossy(comment.as_ref()).into_owned()),
                ),
                Event::Eof => break,
                Event::GeneralRef(reference) => Self::append(
                    &mut roots,
                    &mut stack,
                    XmlNode::Text(format!("&{};", String::from_utf8_lossy(reference.as_ref()))),
                ),
            }
            buffer.clear();
        }
        if !stack.is_empty() {
            return Err("XML document contains unclosed elements".to_string());
        }
        Ok(Self { nodes: roots })
    }

    fn append(roots: &mut Vec<XmlNode>, stack: &mut [XmlElement], node: XmlNode) {
        if let Some(parent) = stack.last_mut() {
            parent.children.push(node);
        } else {
            roots.push(node);
        }
    }
}

struct XmlElement {
    name: String,
    attributes: Vec<XmlAttribute>,
    children: Vec<XmlNode>,
    self_closing: bool,
    preserve_space: bool,
}

impl XmlElement {
    fn from_start(
        reader: &Reader<&[u8]>,
        start: &BytesStart<'_>,
        self_closing: bool,
    ) -> Result<Self, String> {
        let name = String::from_utf8_lossy(start.name().as_ref()).into_owned();
        let mut attributes = Vec::new();
        let mut preserve_space = false;
        for attribute in start.attributes() {
            let attribute = attribute.map_err(|error| error.to_string())?;
            let name = String::from_utf8_lossy(attribute.key.as_ref()).into_owned();
            let value = attribute
                .decoded_and_normalized_value(XmlVersion::Implicit1_0, reader.decoder())
                .map_err(|error| error.to_string())?;
            preserve_space |= name == "xml:space" && value == "preserve";
            attributes.push(XmlAttribute {
                name,
                value: escape(value.as_ref()).into_owned(),
            });
        }
        Ok(Self {
            name,
            attributes,
            children: Vec::new(),
            self_closing,
            preserve_space,
        })
    }

    fn has_text_content(&self) -> bool {
        let has_element = self
            .children
            .iter()
            .any(|child| matches!(child, XmlNode::Element(_)));
        self.children.iter().any(|child| match child {
            XmlNode::Text(text) => self.preserve_space || !text.trim().is_empty() || !has_element,
            XmlNode::CData(_) | XmlNode::ProcessingInstruction(_) => true,
            _ => false,
        })
    }
}

struct XmlAttribute {
    name: String,
    value: String,
}

enum XmlNode {
    Element(XmlElement),
    Text(String),
    CData(String),
    Declaration(String),
    ProcessingInstruction(String),
    DocType(String),
    Comment(String),
}

impl XmlNode {
    fn is_ignorable_whitespace(&self) -> bool {
        matches!(self, Self::Text(text) if text.trim().is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::XmlFormatter;

    #[test]
    fn wraps_android_attributes_and_indents_elements() {
        let input = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<LinearLayout xmlns:android="http://schemas.android.com/apk/res/android" android:orientation="vertical" android:layout_height="wrap_content" android:layout_width="fill_parent"><ImageView android:layout_width="22.0dip" android:id="@id/icon" android:layout_height="22.0dip" /></LinearLayout>
"#;
        let formatted = XmlFormatter::default().format(input).unwrap();
        assert_eq!(
            formatted,
            r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<LinearLayout
    xmlns:android="http://schemas.android.com/apk/res/android"
    android:orientation="vertical"
    android:layout_height="wrap_content"
    android:layout_width="fill_parent">
    <ImageView
        android:layout_width="22.0dip"
        android:id="@id/icon"
        android:layout_height="22.0dip" />
</LinearLayout>
"#
        );
    }

    #[test]
    fn preserves_text_and_mixed_content() {
        let input = r#"<resources><string name="title">Hello <b>world</b>!</string><string name="space">   </string></resources>"#;
        let formatted = XmlFormatter::default().format(input).unwrap();
        assert!(formatted.contains(r#"<string name="title">Hello <b>world</b>!</string>"#));
        assert!(formatted.contains(r#"<string name="space">   </string>"#));
    }
}
