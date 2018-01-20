#[cfg(feature="verify")]
pub use self::absint::*;
#[cfg(feature="verify")]
#[macro_use]
pub mod absint;

#[cfg(not(feature="verify"))]
pub use self::noabsint::*;
#[cfg(not(feature="verify"))]
#[macro_use]
pub mod noabsint;
