use crate::{types::{ClarityInteger, Value, RefinedInteger}, value_ext::ValueExtensions};
use anyhow::{bail, Result, Error};

#[derive(Debug)]
pub enum SExpr {
    Identifier(String),
    LiteralInteger(ClarityInteger),
    RefinedInteger(RefinedInteger),
    Closure(Vec<Self>),

    Define(Define),
    Op(Op),
    TypeDef(Type),
    Literal(Literal),
    Keyword(Keyword),
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
    pub fn eval(&self) -> Result<Vec<Value>> {
        let mut values: Vec<Value> = Default::default();

        if let SExpr::Closure(top_level) = self {
            for expr in top_level {
                eprintln!("evaluating expr: {expr:?}");
                let value = expr.eval_inner()?;
                eprintln!("eval result: {value:?}");
                values.push(value);
            }
        }

        Ok(values)
    }

    fn eval_inner(&self) -> Result<Value> {
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
            SExpr::Literal(lit) => {
                match &lit {
                    Literal::Integer(int) => {
                        match int {
                            ClarityInteger::I128(i) => Ok(Value::Integer(ClarityInteger::I128(*i))),
                            _ => todo!("integer type not implemented")
                        }
                    },
                    _ => todo!("literal type not implemented")
                }
            }
            SExpr::Closure(exprs) => match &exprs[..] {
                // DEFINE-MAP
                [SExpr::Define(Define::Map), name, key_ty, val_ty] => {
                    eprintln!("DEFINE-MAP: name={name:?}, key_ty={key_ty:?}, val_ty={val_ty:?}");
                    Ok(Value::Null)
                },
                // DEFINE READ-ONLY FUNCTION
                [SExpr::Define(Define::ReadOnlyFunction), signature, body] => {
                    eprintln!("DEFINE-READ-ONLY-FUNCTION: signature={signature:?}, body={body:?}");
                    Ok(Value::Null)
                }
                // DEFINE PUBLIC FUNCTION
                [SExpr::Define(Define::PublicFunction), signature, body] => {
                    eprintln!("DEFINE-PUBLIC-FUNCTION: signature={signature:?}, body={body:?}");
                    Ok(Value::Null)
                }
                // DEFINE PRIVATE FUNCTION
                [SExpr::Define(Define::PrivateFunction), signature, body] => {
                    eprintln!("DEFINE-PRIVATE-FUNCTION: signature={signature:?}, body={body:?}");
                    Ok(Value::Null)
                }
                // ADDITION
                [SExpr::Op(Op::Add), init, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval_inner(init), |acc, expr| {
                        acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_add(v))?)
                    })
                }
                // SUBTRACTION
                [SExpr::Op(Op::Sub), init, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval_inner(init), |acc, expr| {
                        acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_sub(v))?)
                    })
                }
                // MULTIPLICATION
                [SExpr::Op(Op::Mul), init, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval_inner(init), |acc, expr| {
                        acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_mul(v))?)
                    })
                }
                // DIVISION
                [SExpr::Op(Op::Div), init, tail @ ..] => {
                    tail.iter().skip(1).fold(Self::eval_inner(init), |acc, expr| {
                        acc.and_then(|a| Self::eval_inner(expr).map(|v| a.checked_div(v))?)
                    })
                }
                [SExpr::Closure(inner), init, tail @ ..] => {
                    eprintln!("\nCLOSURE >>>\nINNER: {inner:?}\nINIT: {init:?}\nTAIL: {tail:?}\n");
                    let mut last_val: Value = match &inner[..] {
                        [SExpr::Define(Define::Map), name, key_ty, val_ty, tail @ ..] => {
                            eprintln!("DEFINE-MAP: name={name:?}, key_ty={key_ty:?}, val_ty={val_ty:?}");
                            Value::Null
                        },
                        _ => bail!("SHIT: {inner:?} TAIL: {tail:?}")
                    };

                    for expr in tail {
                        last_val = Self::eval_inner(expr)?;
                    }
                    //Ok(last_val)
                    bail!("INNER: {inner:?} TAIL: {tail:?}")
                },
                _ => bail!("cannot evaluate list, no match found: {self:?}"),
            },
            _ => bail!("cannot evaluate operator: {self:?}"),
        }
    }
}
