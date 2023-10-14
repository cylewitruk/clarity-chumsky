use clarity::vm::Value;
use anyhow::{Result, bail};

pub trait ValueExtensions {
    fn checked_add(&self, value: Value) -> Result<Value>;
    fn checked_sub(&self, value: Value) -> Result<Value>;
    fn checked_div(&self, value: Value) -> Result<Value>;
    fn checked_mul(&self, value: Value) -> Result<Value>;
}

impl ValueExtensions for Value {
    fn checked_add(&self, value: Value) -> Result<Value> {
        match self {
            Value::Int(i) => {
                if let Value::Int(i2) = value {
                    Ok(Value::Int(i.checked_add(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            Value::UInt(i) => {
                if let Value::UInt(i2) = value {
                    Ok(Value::UInt(i.checked_add(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            }
            _ => bail!("unsupported type")
        }
    }

    fn checked_sub(&self, value: Value) -> Result<Value> {
        match self {
            Value::Int(i) => {
                if let Value::Int(i2) = value {
                    Ok(Value::Int(i.checked_sub(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            Value::UInt(i) => {
                if let Value::UInt(i2) = value {
                    Ok(Value::UInt(i.checked_sub(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            _ => bail!("unsupported type")
        }
    }

    fn checked_div(&self, value: Value) -> Result<Value> {
        match self {
            Value::Int(i) => {
                if let Value::Int(i2) = value {
                    Ok(Value::Int(i.checked_div(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            Value::UInt(i) => {
                if let Value::UInt(i2) = value {
                    Ok(Value::UInt(i.checked_div(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            _ => bail!("unsupported type")
        }
    }

    fn checked_mul(&self, value: Value) -> Result<Value> {
        match self {
            Value::Int(i) => {
                if let Value::Int(i2) = value {
                    Ok(Value::Int(i.checked_mul(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            Value::UInt(i) => {
                if let Value::UInt(i2) = value {
                    Ok(Value::UInt(i.checked_mul(i2).unwrap()))
                } else {
                    bail!("type mismatch")
                }
            },
            _ => bail!("unsupported type")
        }
    }
}

#[test]
fn test_add() {
    let v1 = Value::Int(1);
    let v2 = Value::Int(2);

    let result = v1.checked_add(v2).unwrap();
    assert_eq!(result, Value::Int(3));

    let v3 = Value::UInt(3);

    let result = v1.checked_add(v3).is_err();
    assert!(result);
}