use crate::{types::{ClarityInteger, Value, RefinedInteger}, value_ext::ValueExtensions};
use anyhow::{bail, Result};

#[derive(Debug)]
pub enum SExpr {
    Identifier(String),
    LiteralInteger(ClarityInteger),
    RefinedInteger(RefinedInteger),
    List(Vec<Self>),

    Define(Define),
    Op(Op),
    TypeDef(Type),
    Literal(Literal),
    Keyword(Keyword),
    Delim,

    // Remove these later
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
pub enum Keyword {
    BlockHeight,
    BurnBlockHeight,
    ChainId,
    ContractCaller,
    False,
    IsInMainnet,
    IsInRegTest,
    None,
    StxLiquidSupply,
    True,
    TxSender,
    TxSponsor
}

#[derive(Debug)]
pub enum Define {
    Map,
    DataVar,
    PublicFunction,
    PrivateFunction,
    ReadOnlyFunction
}

#[derive(Debug)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    DefaultTo,
    MapGet,
    Ok,
    MapSet,
}

#[derive(Debug)]
pub enum Literal {
    Int,
    UInt,
    Integer(ClarityInteger),
    AsciiString,
    Utf8String
}

#[derive(Debug)]
pub enum Type {
    Int,
    UInt,
    Bool,
    Principal,
    Buff,
    StringAscii(u32),
    StringUtf8(u32),
    List,
    Tuple,
    Optional,
    Response
}

impl SExpr {
    pub fn eval(&self) -> Result<Value> {
        match self {
            SExpr::LiteralInteger(ty) => Ok(match ty {
                ClarityInteger::I32(i) => Value::Integer(ClarityInteger::I32(*i)),
                ClarityInteger::U32(i) => Value::Integer(ClarityInteger::U32(*i)),
                ClarityInteger::I64(i) => Value::Integer(ClarityInteger::I64(*i)),
                ClarityInteger::U64(i) => Value::Integer(ClarityInteger::U64(*i)),
                // These are the default integer types in Clarity which we are
                // remapping to the `Integer` variant. `Value::Int` and `Value::UInt`
                // become aliases.
                ClarityInteger::I128(i) => Value::Integer(ClarityInteger::I128(*i)),
                ClarityInteger::U128(i) => Value::Integer(ClarityInteger::U128(*i)),
                // The Clarity `Value` type would need to be extended to have a type
                // similar to the `ClarityInteger` type here in order to support
                // integers larger than 128 bits. We use our simulated `Value` type here.
                ClarityInteger::I256(i) => Value::Integer(ClarityInteger::I256(i.clone())),
                ClarityInteger::U256(i) => Value::Integer(ClarityInteger::U256(i.clone())),
                ClarityInteger::I512(i) => Value::Integer(ClarityInteger::I512(i.clone())),
                ClarityInteger::U512(i) => Value::Integer(ClarityInteger::U512(i.clone())),
            }),
            SExpr::Identifier(id) => {
                todo!("identifier not implemented");
            },
            SExpr::Define(def) => match def {
                Define::Map => todo!(),
                Define::DataVar => todo!(),
                Define::PublicFunction => todo!(),
                Define::PrivateFunction => todo!(),
                Define::ReadOnlyFunction => todo!(),
            },
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
                [SExpr::List(list), tail @ ..] => {
                    bail!("\nLIST: \n{list:?}\n\nTAIL: \n{tail:?}\n");
                }
                _ => bail!("cannot evaluate list, no match found: {self:?}"),
            },
            _ => bail!("cannot evaluate operator: {self:?}"),
        }
    }
}
