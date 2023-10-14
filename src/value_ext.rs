use anyhow::{bail, Result};
use clarity::vm::Value;

use crate::{errors::ClarityError, types::{ClarityType, IntegerType}};

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
            _ => todo!(),
        }
    }
}
