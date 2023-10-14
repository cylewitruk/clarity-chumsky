use crate::{value_ext::ValueExtensions, types::ClarityInteger};
use anyhow::{bail, Result};
use clarity::vm::Value;

#[derive(Debug)]
pub enum SExpr {
    LiteralInteger(ClarityInteger),
    List(Vec<Self>),
    Add,
    Sub,
    Mul,
    Div,
}

impl SExpr {
    pub fn eval(&self) -> Result<Value> {
        match self {
            SExpr::LiteralInteger(ty) => Ok(match ty {
                ClarityInteger::I32(i) => Value::Int((*i).into()),
                ClarityInteger::U32(i) => Value::Int((*i).into()),
                ClarityInteger::I64(i) => Value::Int((*i).into()),
                ClarityInteger::U64(i) => Value::Int((*i).into()),
                ClarityInteger::I128(i) => Value::Int(*i),
                ClarityInteger::U128(i) => Value::UInt(*i),
                // The Clarity `Value` type would need to be extended to have a type
                // similar to the `ClarityInteger` type here in order to support
                // integers larger than 128 bits.
                ClarityInteger::I256(_) => unimplemented!(),
                ClarityInteger::U256(_) => unimplemented!(),
                ClarityInteger::I512(_) => unimplemented!(),
                ClarityInteger::U512(_) => unimplemented!(),
            }),
            SExpr::List(list) => match &list[..] {
                // ADDITION
                [SExpr::Add, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval(&tail[0]), |acc, expr| {
                        acc.and_then(|a| Self::eval(expr).map(|v| a.checked_add(v))?)
                    })
                }
                // SUBTRACTION
                [SExpr::Sub, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval(&tail[0]), |acc, expr| {
                        acc.and_then(|a| Self::eval(expr).map(|v| a.checked_sub(v))?)
                    })
                }
                // MULTIPLICATION
                [SExpr::Mul, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval(&tail[0]), |acc, expr| {
                        acc.and_then(|a| Self::eval(expr).map(|v| a.checked_mul(v))?)
                    })
                }
                // DIVISION
                [SExpr::Div, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval(&tail[0]), |acc, expr| {
                        acc.and_then(|a| Self::eval(expr).map(|v| a.checked_div(v))?)
                    })
                }
                _ => bail!("cannot evaluate list, no match found"),
            },
            _ => bail!("cannot evaluate operator: {self:?}"),
        }
    }
}
