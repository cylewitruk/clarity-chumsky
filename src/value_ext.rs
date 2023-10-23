use anyhow::{anyhow, bail, Result};

use crate::{
    errors::ClarityError,
    ast::Integer,
    types::{ClarityType, IntegerType, Value},
};

pub trait ValueExtensions {
    fn checked_add(&self, value: Value) -> Result<Value>;
    fn checked_sub(&self, value: Value) -> Result<Value>;
    fn checked_div(&self, value: Value) -> Result<Value>;
    fn checked_mul(&self, value: Value) -> Result<Value>;

    fn ty(&self) -> ClarityType;
}

impl ValueExtensions for Value {
    fn checked_add(&self, value: Value) -> Result<Value> {
        match (self, &value) {
            (Value::Int(i), Value::Int(i2)) => Ok(Value::Int(i.checked_add(*i2).unwrap())),
            (Value::UInt(i), Value::UInt(i2)) => Ok(Value::UInt(i.checked_add(*i2).unwrap())),
            (Value::Integer(Integer::I128(a)), Value::Integer(Integer::I128(b))) => a
                .checked_add(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticOverflow))
                .map(|i| Value::Integer(Integer::I128(i))),
            _ => bail!(ClarityError::TypeMismatch {
                expected: self.ty(),
                received: value.ty()
            }),
        }
    }

    fn checked_sub(&self, value: Value) -> Result<Value> {
        match (self, &value) {
            (Value::Int(i), Value::Int(i2)) => Ok(Value::Int(i.checked_sub(*i2).unwrap())),
            (Value::UInt(i), Value::UInt(i2)) => Ok(Value::UInt(i.checked_sub(*i2).unwrap())),
            (Value::Integer(Integer::I128(a)), Value::Integer(Integer::I128(b))) => a
                .checked_sub(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticUnderflow))
                .map(|i| Value::Integer(Integer::I128(i))),
            _ => bail!(ClarityError::TypeMismatch {
                expected: self.ty(),
                received: value.ty()
            }),
        }
    }

    fn checked_div(&self, value: Value) -> Result<Value> {
        match (self, &value) {
            (Value::Int(i), Value::Int(i2)) => Ok(Value::Int(i.checked_div(*i2).unwrap())),
            (Value::UInt(i), Value::UInt(i2)) => Ok(Value::UInt(i.checked_div(*i2).unwrap())),
            (Value::Integer(Integer::I128(a)), Value::Integer(Integer::I128(b))) => a
                .checked_div(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticUnderflow))
                .map(|i| Value::Integer(Integer::I128(i))),
            _ => bail!(ClarityError::TypeMismatch {
                expected: self.ty(),
                received: value.ty()
            }),
        }
    }

    fn checked_mul(&self, value: Value) -> Result<Value> {
        match (self, &value) {
            (Value::Int(i), Value::Int(i2)) => Ok(Value::Int(i.checked_mul(*i2).unwrap())),
            (Value::UInt(i), Value::UInt(i2)) => Ok(Value::UInt(i.checked_mul(*i2).unwrap())),
            (Value::Integer(Integer::I128(a)), Value::Integer(Integer::I128(b))) => a
                .checked_mul(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticOverflow))
                .map(|i| Value::Integer(Integer::I128(i))),
            _ => bail!(ClarityError::TypeMismatch {
                expected: self.ty(),
                received: value.ty()
            }),
        }
    }

    fn ty(&self) -> ClarityType {
        match self {
            Value::Bool(_) => ClarityType::Bool,
            Value::CallableContract(_) => ClarityType::CallableContract,
            Value::Int(_) => ClarityType::Integer(IntegerType::I128),
            Value::UInt(_) => ClarityType::Integer(IntegerType::U128),
            Value::Integer(i) => match i {
                Integer::I32(_) => ClarityType::Integer(IntegerType::I32),
                Integer::U32(_) => ClarityType::Integer(IntegerType::U32),
                Integer::I64(_) => ClarityType::Integer(IntegerType::I64),
                Integer::U64(_) => ClarityType::Integer(IntegerType::U64),
                Integer::I128(_) => ClarityType::Integer(IntegerType::I128),
                Integer::U128(_) => ClarityType::Integer(IntegerType::U128),
                Integer::I256(_) => ClarityType::Integer(IntegerType::I256),
                Integer::U256(_) => ClarityType::Integer(IntegerType::U256),
                Integer::I512(_) => ClarityType::Integer(IntegerType::I512),
                Integer::U512(_) => ClarityType::Integer(IntegerType::U512),
            },
            Value::Null => ClarityType::Void,
        }
    }
}
