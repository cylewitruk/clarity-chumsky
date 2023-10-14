use clarity::vm::Value;

use crate::{tokens::IntegerType, value_ext::ValueExtensions};
use anyhow::{bail, Result};

#[derive(Debug)]
pub enum SExpr {
    LiteralInteger(IntegerType),
    List(Vec<Self>),

    // Operators
    Add,
    Sub,
    Mul,
    Div,
}

impl SExpr {
    // Recursively evaluate an s-expression
    pub fn eval(&self) -> Result<Value> {
        match self {
            SExpr::LiteralInteger(ty) => match ty {
                IntegerType::I128(i) => Ok(Value::Int(*i)),
                IntegerType::U128(i) => Ok(Value::UInt(*i)),
            },
            SExpr::List(list) => match &list[..] {
                [SExpr::Add, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            let val = Self::eval(expr)?;
                            val.checked_add(acc.unwrap())
                        }
                    )
                }
                [SExpr::Sub, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            let val = Self::eval(expr)?;
                            acc.unwrap().checked_sub(val)
                        }
                    )
                }
                [SExpr::Mul, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            let val = Self::eval(expr)?;
                            val.checked_mul(acc.unwrap())
                        }
                    )
                }
                [SExpr::Div, tail @ ..] => {
                    tail[1..].iter().fold(
                        Self::eval(&tail[0]),
                        |acc, expr| {
                            let val = Self::eval(expr)?;
                            acc.unwrap().checked_div(val)
                        }
                    )
                }
                _ => bail!("cannot evaluate list, no match found"),
            },
            _ => bail!("cannot evaluate operator: {self:?}")
        }
    }
}
