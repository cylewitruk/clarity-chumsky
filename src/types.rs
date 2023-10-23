use core::fmt;
use std::num::TryFromIntError;

use clarity::vm::types::CallableData;
use lazy_static::*;
use num_bigint::{BigInt, BigUint, TryFromBigIntError};

use crate::ast::Integer;

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
    //RefinedInteger(RefinedInteger),
    CallableContract,
    Void,
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
    U512,
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Integer::I32(i) => write!(f, "{}", i),
            Integer::U32(i) => write!(f, "{}", i),
            Integer::I64(i) => write!(f, "{}", i),
            Integer::U64(i) => write!(f, "{}", i),
            Integer::I128(i) => write!(f, "{}", i),
            Integer::U128(i) => write!(f, "{}", i),
            Integer::I256(i) => write!(f, "{}", i),
            Integer::U256(i) => write!(f, "{}", i),
            Integer::I512(i) => write!(f, "{}", i),
            Integer::U512(i) => write!(f, "{}", i),
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
    Integer(Integer),
    CallableContract(CallableData),
    Null,
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

#[derive(Debug, Clone, PartialEq)]
pub struct RefinedInteger {
    pub low_val: Integer,
    pub high_val: Integer,
}

impl RefinedInteger {
    pub fn new(low_val: Integer, high_val: Integer) -> Self {
        Self { low_val, high_val }
    }
}

impl From<i32> for Integer {
    fn from(val: i32) -> Self {
        Integer::I32(val)
    }
}

impl From<u32> for Integer {
    fn from(val: u32) -> Self {
        Integer::U32(val)
    }
}

impl From<i64> for Integer {
    fn from(val: i64) -> Self {
        Integer::I64(val)
    }
}

impl From<u64> for Integer {
    fn from(val: u64) -> Self {
        Integer::U64(val)
    }
}

impl From<i128> for Integer {
    fn from(val: i128) -> Self {
        Integer::I128(val)
    }
}

impl From<u128> for Integer {
    fn from(val: u128) -> Self {
        Integer::U128(val)
    }
}

impl TryInto<Integer> for &str {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<Integer, Self::Error> {
        if self.chars().nth(0) == Some('-') {
            let bint = BigInt::parse_bytes(self.as_bytes(), 10);
            let result: Integer = bint.try_into()?;
            Ok(result)
        } else {
            let bint = BigUint::parse_bytes(self.as_bytes(), 10);
            let result: Integer = bint.try_into()?;
            Ok(result)
        }
    }
}

impl TryInto<Integer> for BigInt {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<Integer, Self::Error> {
        if self >= i32::MIN.into() && self <= i32::MAX.into() {
            let val: i32 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigInt)?;
            Ok(Integer::I32(val))
        } else if self >= i64::MIN.into() && self <= i64::MAX.into() {
            let val: i64 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigInt)?;
            Ok(Integer::I64(val))
        } else if self >= i128::MIN.into() && self <= i128::MAX.into() {
            let val: i128 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigInt)?;
            Ok(Integer::I128(val))
        } else if self >= *I256_MIN && self <= *I256_MAX {
            Ok(Integer::I256(self))
        } else if self >= *I512_MIN && self <= *I512_MAX {
            Ok(Integer::I512(self))
        } else {
            Err(TryIntoClarityIntError::BigIntOutOfRange(self))
        }
    }
}

impl TryInto<Integer> for Option<BigUint> {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<Integer, Self::Error> {
        if let Some(val) = self {
            let x: Integer = val.try_into()?;
            return Ok(x);
        }
        Err(TryIntoClarityIntError::UIntCannotBeLessThanZero)
    }
}

impl TryInto<Integer> for Option<BigInt> {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<Integer, Self::Error> {
        if let Some(val) = self {
            let x: Integer = val.try_into()?;
            return Ok(x);
        }
        Err(TryIntoClarityIntError::UIntCannotBeLessThanZero)
    }
}

impl TryInto<Integer> for BigUint {
    type Error = TryIntoClarityIntError;

    fn try_into(self) -> Result<Integer, Self::Error> {
        if self < 0u8.into() {
            return Err(TryIntoClarityIntError::UIntCannotBeLessThanZero);
        }

        if self >= 0u8.into() && self <= u32::MAX.into() {
            let val: u32 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigUInt)?;
            Ok(Integer::U32(val))
        } else if self >= 0u8.into() && self <= u64::MAX.into() {
            let val: u64 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigUInt)?;
            Ok(Integer::U64(val))
        } else if self >= 0u8.into() && self <= u128::MAX.into() {
            let val: u128 = self
                .try_into()
                .map_err(TryIntoClarityIntError::FromBigUInt)?;
            Ok(Integer::U128(val))
        } else if self >= 0u8.into() && self <= *U256_MAX {
            Ok(Integer::U256(self))
        } else if self >= 0u8.into() && self <= *U512_MAX {
            Ok(Integer::U512(self))
        } else {
            panic!("integer type not supported (out of range)");
        }
    }
}

impl TryInto<i32> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i32, Self::Error> {
        match self {
            Integer::I32(i) => Ok(i),
            Integer::U32(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<u32> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u32, Self::Error> {
        match self {
            Integer::I32(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U32(i) => Ok(i),
            Integer::I64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<i64> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i64, Self::Error> {
        match self {
            Integer::I32(i) => Ok(i.into()),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => Ok(i),
            Integer::U64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<u64> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u64, Self::Error> {
        match self {
            Integer::I32(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U64(i) => Ok(i),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<i128> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<i128, Self::Error> {
        match self {
            Integer::I32(i) => Ok(i.into()),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => Ok(i.into()),
            Integer::U64(i) => Ok(i.into()),
            Integer::I128(i) => Ok(i),
            Integer::U128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<u128> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<u128, Self::Error> {
        match self {
            Integer::I32(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U64(i) => Ok(i.into()),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromInt),
            Integer::U128(i) => Ok(i),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigUInt),
        }
    }
}

impl TryInto<BigInt> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<BigInt, Self::Error> {
        match self {
            Integer::I32(i) => Ok(i.into()),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => Ok(i.into()),
            Integer::U64(i) => Ok(i.into()),
            Integer::I128(i) => Ok(i.into()),
            Integer::U128(i) => Ok(i.into()),
            Integer::I256(i) => Ok(i),
            Integer::U256(i) => Ok(i.into()),
            Integer::I512(i) => Ok(i),
            Integer::U512(i) => Ok(i.into()),
        }
    }
}

impl TryInto<BigUint> for Integer {
    type Error = TryFromClarityIntError;

    fn try_into(self) -> Result<BigUint, Self::Error> {
        match self {
            Integer::I32(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt2),
            Integer::U32(i) => Ok(i.into()),
            Integer::I64(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt2),
            Integer::U64(i) => Ok(i.into()),
            Integer::I128(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt2),
            Integer::U128(i) => Ok(i.into()),
            Integer::I256(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U256(i) => Ok(i),
            Integer::I512(i) => i.try_into().map_err(TryFromClarityIntError::FromBigInt),
            Integer::U512(i) => Ok(i),
        }
    }
}
