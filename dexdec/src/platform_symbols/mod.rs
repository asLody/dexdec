//! Versioned platform ABI metadata.
//!
//! Platform symbols are immutable facts obtained from class files. They
//! constrain type and source recovery but never infer control-flow meaning.

use std::io;
use std::path::Path;
use std::sync::{Arc, OnceLock};

#[cfg(feature = "symbol-builder")]
mod android;
#[cfg(feature = "symbol-builder")]
mod builder;
#[cfg(feature = "symbol-builder")]
mod classfile;
mod codec;
mod model;

#[cfg(feature = "symbol-builder")]
pub use android::AndroidMetadataStats;
#[cfg(feature = "symbol-builder")]
pub use builder::{PlatformSymbolBuilder, SymbolArchive, SymbolBuildStats};
pub use codec::DexSymbolsCodec;
pub use model::{
    PlatformAnnotation, PlatformAnnotationValue, PlatformClass, PlatformConstant,
    PlatformConstantDomain, PlatformConstantKind, PlatformConstantMember, PlatformFamily,
    PlatformField, PlatformFieldReference, PlatformMethod, PlatformNullability,
    PlatformSymbolDatabase, PlatformSymbolSet, PlatformTarget, SymbolAvailability,
    SymbolDatabaseStats, SymbolProvider, SymbolSource,
};

const EMBEDDED_SYMBOLS: &[u8] = include_bytes!("../../resources/symbols/platform.dexsym");

/// Returns the process-wide target-selected platform ABI.
///
/// The immutable database is decoded once. `DEXDEC_SYMBOLS` may point at a
/// compatible `.dexsym` file before the first request.
pub fn default_platform_symbols() -> io::Result<Arc<PlatformSymbolSet>> {
    static DEFAULT: OnceLock<Arc<PlatformSymbolSet>> = OnceLock::new();
    if let Some(symbols) = DEFAULT.get() {
        return Ok(Arc::clone(symbols));
    }
    let database = match std::env::var_os("DEXDEC_SYMBOLS") {
        Some(path) => PlatformSymbolDatabase::read(Path::new(&path))?,
        None => PlatformSymbolDatabase::from_bytes(EMBEDDED_SYMBOLS)?,
    };
    let symbols = Arc::new(database.select(database.default_target()));
    match DEFAULT.set(Arc::clone(&symbols)) {
        Ok(()) => Ok(symbols),
        Err(_) => DEFAULT.get().map(Arc::clone).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "platform symbol cache publication failed",
            )
        }),
    }
}
