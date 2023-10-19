use anyhow::{anyhow, bail, Result};

use crate::{
    errors::ClarityError,
    types::{ClarityInteger, ClarityType, IntegerType, Value}, ast::Op,
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
            (Value::Integer(ClarityInteger::I128(a)), Value::Integer(ClarityInteger::I128(b))) => a
                .checked_add(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticOverflow { op: Op::Add }))
                .map(|i| Value::Integer(ClarityInteger::I128(i))),
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
            (Value::Integer(ClarityInteger::I128(a)), Value::Integer(ClarityInteger::I128(b))) => a
                .checked_sub(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticUnderflow { op: Op::Sub }))
                .map(|i| Value::Integer(ClarityInteger::I128(i))),
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
            (Value::Integer(ClarityInteger::I128(a)), Value::Integer(ClarityInteger::I128(b))) => a
                .checked_div(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticUnderflow { op: Op::Div }))
                .map(|i| Value::Integer(ClarityInteger::I128(i))),
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
            (Value::Integer(ClarityInteger::I128(a)), Value::Integer(ClarityInteger::I128(b))) => a
                .checked_mul(*b)
                .ok_or(anyhow!(ClarityError::ArithmeticOverflow { op: Op::Mul }))
                .map(|i| Value::Integer(ClarityInteger::I128(i))),
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
                ClarityInteger::I32(_) => ClarityType::Integer(IntegerType::I32),
                ClarityInteger::U32(_) => ClarityType::Integer(IntegerType::U32),
                ClarityInteger::I64(_) => ClarityType::Integer(IntegerType::I64),
                ClarityInteger::U64(_) => ClarityType::Integer(IntegerType::U64),
                ClarityInteger::I128(_) => ClarityType::Integer(IntegerType::I128),
                ClarityInteger::U128(_) => ClarityType::Integer(IntegerType::U128),
                ClarityInteger::I256(_) => ClarityType::Integer(IntegerType::I256),
                ClarityInteger::U256(_) => ClarityType::Integer(IntegerType::U256),
                ClarityInteger::I512(_) => ClarityType::Integer(IntegerType::I512),
                ClarityInteger::U512(_) => ClarityType::Integer(IntegerType::U512),
            },
            Value::Null => ClarityType::Void,
        }
    }
}
