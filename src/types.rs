use core::fmt;
use std::num::TryFromIntError;

use clarity::vm::types::CallableData;
use lazy_static::*;
use num_bigint::{BigInt, BigUint, TryFromBigIntError};

// Constants
lazy_static! {
    /// **Min**imum value for a 256-bit **signed** integer.
    pub static ref I256_MIN: BigInt = BigInt::parse_bytes(
        "-57896044618658097711785492504343953926634992332820282019728792003956564819968".as_bytes(),
        10
    )
    .unwrap();

    /// **Max**imum value for a 256-bit **unsigned** integer.
    pub static ref U256_MAX: BigUint = BigUint::parse_bytes(
        "115792089237316195423570985008687907853269984665640564039457584007913129639935".as_bytes(),
        10
    )
    .unwrap();

    /// Maximum value for a 256-bit **signed** integer.
    pub static ref I256_MAX: BigInt = BigInt::parse_bytes(
        "57896044618658097711785492504343953926634992332820282019728792003956564819967".as_bytes(),
        10
    )
    .unwrap();

    /// Minimum value for a 256-bit **signed** integer.
    pub static ref I512_MIN: BigInt = BigInt::parse_bytes(
        concat!(
            r#"-6703903964971298549787012499102923063739682910296196688861780721860882015036773"#,
            r#"488400937149083451713845015929093243025426876941405973284973216824503042048"#
        )
        .as_bytes(),
        10
    )
    .unwrap();

    /// Maximum value for a 512-bit **signed** integer.
    pub static ref I512_MAX: BigInt = BigInt::parse_bytes(
        concat!(
            r#"670390396497129854978701249910292306373968291029619668886178072186088201503677"#,
            r#"r#"3488400937149083451713845015929093243025426876941405973284973216824503042047"#
        )
        .as_bytes(),
        10
    )
    .unwrap();

    /// Maximum value for a 512-bit **unsigned** integer.
    pub static ref U512_MAX: BigUint = BigUint::parse_bytes(
        concat!(
            r#"13407807929942597099574024998205846127479365820592393377723561443721764030073546"#,
            r#"976801874298166903427690031858186486050853753882811946569946433649006084095"#
        )
        .as_bytes(),
        10
    )
    .unwrap();
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClarityType {
    Bool,
    Integer(IntegerType),
    RefinedInteger(RefinedInteger),
    CallableContract,
    Void
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IntegerType {
    I32,
    U32,
    I64,
    U64,
    I128,
    U128,
    I256,
    U256,
    I512,
    U512
}

/// Enum variants for the different Clarity integer types.
#[derive(Debug, Clone, PartialEq)]
pub enum ClarityInteger {
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    I128(i128),
    U128(u128),
    I256(BigInt),
    U256(BigUint),
    I512(BigInt),
    U512(BigUint),
}

impl fmt::Display for ClarityInteger {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClarityInteger::I32(i) => write!(f, "{}", i),
            ClarityInteger::U32(i) => write!(f, "{}", i),
            ClarityInteger::I64(i) => write!(f, "{}", i),
            ClarityInteger::U64(i) => write!(f, "{}", i),
            ClarityInteger::I128(i) => write!(f, "{}", i),
            ClarityInteger::U128(i) => write!(f, "{}", i),
            ClarityInteger::I256(i) => write!(f, "{}", i),
            ClarityInteger::U256(i) => write!(f, "{}", i),
            ClarityInteger::I512(i) => write!(f, "{}", i),
            ClarityInteger::U512(i) => write!(f, "{}", i),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
/// This enum simulates the Clarity `Value` enum since we cannot extend it
/// from this crate.
pub enum Value {
    Bool(bool),
    Int(i128),
    UInt(u128),
    Integer(ClarityInteger),
    CallableContract(CallableData),
    Null
}

#[derive(Debug, Clone, PartialEq)]
pub enum TryFromClarityIntError {
    FromInt(TryFromIntError),
    FromBigInt(TryFromBigIntError<BigInt>),
    FromBigUInt(TryFromBigIntError<BigUint>),
    FromBigInt2(TryFromBigIntError<()>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TryIntoClarityIntError {
    BigIntOutOfRange(BigInt),
    BigUIntOutOfRange(BigUint),
    UIntCannotBeLessThanZero,
    FromBigInt(TryFromBigIntError<BigInt>),
    FromBigUInt(TryFromBigIntError<BigUint>),
}

#[derive(Debug)]
pub enum FunctionKind {
    Public,
    Private,
    ReadOnly
}

#[derive(Debug, Clone, PartialEq)]
pub struct RefinedInteger {
    pub low_val: ClarityInteger,
    pub high_val: ClarityInteger,
}

impl RefinedInteger {
    pub fn new(low_val: ClarityInteger, high_val: ClarityInteger) -> Self {
        Self { low_val, high_val }
    }
}

impl Into<ClarityInteger> for i32 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::I32(self)
    }
}

impl Into<ClarityInteger> for u32 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::U32(self)
    }
}

impl Into<ClarityInteger> for i64 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::I64(self)
    }
}

impl Into<ClarityInteger> for u64 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::U64(self)
    }
}

impl Into<ClarityInteger> for i128 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::I128(self)
    }
}

impl Into<ClarityInteger> for u128 {
    fn into(self) -> ClarityInteger {
        ClarityInteger::U128(self)
    }
}

impl TryInto<ClarityInteger> for &str {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<ClarityInteger, Self::Error> {
        if self.chars().nth(0) == Some('-') {
            let bint = BigInt::parse_bytes(self.as_bytes(), 10);
            let result: ClarityInteger = bint.try_into()?;
            return Ok(result);
        } else {
            let bint = BigUint::parse_bytes(self.as_bytes(), 10);
            let result: ClarityInteger = bint.try_into()?;
            return Ok(result);
        }
    }
}

impl TryInto<ClarityInteger> for BigInt {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<ClarityInteger, Self::Error> {
        if self >= i32::MIN.into() && self <= i32::MAX.into() {
            let val: i32 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigInt(e))?;
            Ok(ClarityInteger::I32(val))
        } else if self >= i64::MIN.into() && self <= i64::MAX.into() {
            let val: i64 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigInt(e))?;
            Ok(ClarityInteger::I64(val))
        } else if self >= i128::MIN.into() && self <= i128::MAX.into() {
            let val: i128 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigInt(e))?;
            Ok(ClarityInteger::I128(val))
        } else if self >= *I256_MIN && self <= *I256_MAX {
            Ok(ClarityInteger::I256(self))
        } else if self >= *I512_MIN && self <= *I512_MAX {
            Ok(ClarityInteger::I512(self))
        } else {
            Err(TryIntoClarityIntError::BigIntOutOfRange(self))
        }
    }
}

impl TryInto<ClarityInteger> for Option<BigUint> {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<ClarityInteger, Self::Error> {
        if let Some(val) = self {
            let x: ClarityInteger = val.try_into()?;
            return Ok(x);
        }
        return Err(TryIntoClarityIntError::UIntCannotBeLessThanZero);
    }
}

impl TryInto<ClarityInteger> for Option<BigInt> {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<ClarityInteger, Self::Error> {
        if let Some(val) = self {
            let x: ClarityInteger = val.try_into()?;
            return Ok(x);
        }
        return Err(TryIntoClarityIntError::UIntCannotBeLessThanZero);
    }
}

impl TryInto<ClarityInteger> for BigUint {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<ClarityInteger, Self::Error> {
        if self < 0u8.into() {
            return Err(TryIntoClarityIntError::UIntCannotBeLessThanZero);
        }

        if self >= 0u8.into() && self <= u32::MAX.into() {
            let val: u32 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigUInt(e))?;
            Ok(ClarityInteger::U32(val))
        } else if self >= 0u8.into() && self <= u64::MAX.into() {
            let val: u64 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigUInt(e))?;
            Ok(ClarityInteger::U64(val))
        } else if self >= 0u8.into() && self <= u128::MAX.into() {
            let val: u128 = self
                .try_into()
                .map_err(|e| TryIntoClarityIntError::FromBigUInt(e))?;
            Ok(ClarityInteger::U128(val))
        } else if self >= 0u8.into() && self <= *U256_MAX {
            Ok(ClarityInteger::U256(self))
        } else if self >= 0u8.into() && self <= *U512_MAX {
            Ok(ClarityInteger::U512(self))
        } else {
            panic!("integer type not supported (out of range)");
        }
    }
}

impl TryInto<i32> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i32, Self::Error> {
        match self {
            ClarityInteger::I32(i) => Ok(i),
            ClarityInteger::U32(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<u32> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u32, Self::Error> {
        match self {
            ClarityInteger::I32(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U32(i) => Ok(i),
            ClarityInteger::I64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<i64> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i64, Self::Error> {
        match self {
            ClarityInteger::I32(i) => Ok(i.into()),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => Ok(i),
            ClarityInteger::U64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<u64> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u64, Self::Error> {
        match self {
            ClarityInteger::I32(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U64(i) => Ok(i),
            ClarityInteger::I128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<i128> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i128, Self::Error> {
        match self {
            ClarityInteger::I32(i) => Ok(i.into()),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => Ok(i.into()),
            ClarityInteger::U64(i) => Ok(i.into()),
            ClarityInteger::I128(i) => Ok(i),
            ClarityInteger::U128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<u128> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u128, Self::Error> {
        match self {
            ClarityInteger::I32(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U64(i) => Ok(i.into()),
            ClarityInteger::I128(i) => i.try_into().map_err(|e| TryFromClarityIntError::FromInt(e)),
            ClarityInteger::U128(i) => Ok(i),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigUInt(e)),
        }
    }
}

impl TryInto<BigInt> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<BigInt, Self::Error> {
        match self {
            ClarityInteger::I32(i) => Ok(i.into()),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => Ok(i.into()),
            ClarityInteger::U64(i) => Ok(i.into()),
            ClarityInteger::I128(i) => Ok(i.into()),
            ClarityInteger::U128(i) => Ok(i.into()),
            ClarityInteger::I256(i) => Ok(i.into()),
            ClarityInteger::U256(i) => Ok(i.into()),
            ClarityInteger::I512(i) => Ok(i.into()),
            ClarityInteger::U512(i) => Ok(i.into()),
        }
    }
}

impl TryInto<BigUint> for ClarityInteger {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<BigUint, Self::Error> {
        match self {
            ClarityInteger::I32(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt2(e)),
            ClarityInteger::U32(i) => Ok(i.into()),
            ClarityInteger::I64(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt2(e)),
            ClarityInteger::U64(i) => Ok(i.into()),
            ClarityInteger::I128(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt2(e)),
            ClarityInteger::U128(i) => Ok(i.into()),
            ClarityInteger::I256(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U256(i) => Ok(i.into()),
            ClarityInteger::I512(i) => i
                .try_into()
                .map_err(|e| TryFromClarityIntError::FromBigInt(e)),
            ClarityInteger::U512(i) => Ok(i.into()),
        }
    }
}
