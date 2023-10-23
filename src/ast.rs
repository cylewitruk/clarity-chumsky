use num_bigint::{BigInt, BigUint};

use crate::types::{RefinedInteger};

/// Clarity expression types.
#[derive(Debug, Clone, PartialEq)]
pub enum SExpr<'a> {
    Error,

    Identifier(Box<Identifier<'a>>),
    Closure(Vec<Self>),
    Define(Define<'a>),
    Op(Op<'a>),
    TypeDef(Type),
    Literal(Literal<'a>),
    Keyword(Keyword),
    Tuple(Vec<ArgDef<'a>>),
}

/// Enum variants for the different integer types.
#[derive(Debug, Clone, PartialEq)]
pub enum Integer {
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

/// Clarity keywords.
#[derive(Debug, Clone, Copy, PartialEq)]
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
    TxSponsor,
}

/// Clarity `define` statements.
#[derive(Debug, Clone, PartialEq)]
pub enum Define<'a> {
    Map(MapDef<'a>),
    DataVar,
    PublicFunction(Box<FuncDef<'a>>),
    PrivateFunction(Box<FuncDef<'a>>),
    ReadOnlyFunction(Box<FuncDef<'a>>),
    Tuple(TupleDef<'a>),
}

/// Clarity operations (functions).
#[derive(Debug, Clone, PartialEq)]
pub enum Op<'a> {
    Add(Vec<SExpr<'a>>),
    Sub(Vec<SExpr<'a>>),
    Mul(Vec<SExpr<'a>>),
    Div(Vec<SExpr<'a>>),
    DefaultTo(DefaultToDef<'a>),
    MapGet,
    Ok(Box<SExpr<'a>>),
    Err(Box<SExpr<'a>>),
    MapSet { name: &'a str, key: Box<SExpr<'a>>, value: Box<SExpr<'a>> },
}

/// Clarity literals.
#[derive(Debug, Clone, PartialEq)]
pub enum Literal<'a> {
    Int(i128),
    UInt(u128),
    Bool(bool),
    Integer(Integer),
    AsciiString(&'a str),
    Utf8String(&'a str),
    Principal(&'a str),
}

/// Clarity type definitions.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,    // Legacy i128
    UInt,   // Legay u128
    Bool,
    Principal,
    Buffer(u32),
    StringAscii(u32),
    StringUtf8(u32),
    List { max_len: u32, ty: Box<Type> },
    Optional(Box<Type>),
    Response { ok_ty: Box<Type>, err_ty: Box<Type> },
    RefinedInteger(RefinedInteger),
    Void
}

/// Clarity identifiers.
#[derive(Debug, Clone, PartialEq)]
pub enum Identifier<'a> {
    String(&'a str),
    Expr(SExpr<'a>),
}

/// Clarity map definition.
#[derive(Debug, Clone, PartialEq)]
pub struct MapDef<'a> {
    pub name: &'a str,
    pub key_ty: Type,
    pub val_ty: Type,
}

/// Clarity function definition.
#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef<'a> {
    pub signature: FuncSignature<'a>,
    pub body: SExpr<'a>,
}

/// Clarity function kind (visibility).
#[derive(Debug, Clone, PartialEq)]
pub enum FuncKind {
    Public,
    Private,
    ReadOnly,
}

/// Clarity function signature (name and arguments, without the body).
#[derive(Debug, Clone, PartialEq)]
pub struct FuncSignature<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}

/// Clarity argument definition (name + type).
#[derive(Debug, Clone, PartialEq)]
pub struct ArgDef<'a> {
    pub name: &'a str,
    pub ty: Type,
}

/// `default-to` definition.
#[derive(Debug, Clone, PartialEq)]
pub struct DefaultToDef<'a> {
    pub default: Box<SExpr<'a>>,
    pub tail: Box<SExpr<'a>>,
}

/// `tuple` definition.
#[derive(Debug, Clone, PartialEq)]
pub struct TupleDef<'a> {
    pub name: &'a str,
    pub args: Vec<ArgDef<'a>>,
}

impl<'a> From<Literal<'a>> for SExpr<'a> {
    fn from(value: Literal<'a>) -> Self {
        SExpr::Literal(value)
    }
}

impl<'a> From<Type> for SExpr<'a> {
    fn from(value: Type) -> Self {
        SExpr::TypeDef(value)
    }
}

impl<'a> From<Op<'a>> for SExpr<'a> {
    fn from(value: Op<'a>) -> Self {
        SExpr::Op(value)
    }
}

impl<'a> From<Integer> for SExpr<'a> {
    fn from(value: Integer) -> Self {
        Literal::Integer(value).into()
    }
}

impl SExpr<'_> {
    pub fn return_ty(&self) -> Type {
        match self {
            SExpr::Error | SExpr::Define(_) | SExpr::Identifier(_) => Type::Void,
            SExpr::Literal(lit) => lit.into(),
            SExpr::Op(op) => { todo!() },
            _ => todo!()
        }
    }
}

impl<'a> From<&Literal<'a>> for Type {
    fn from(value: &Literal<'a>) -> Self {
        match value {
            Literal::AsciiString(str) => Type::StringAscii(str.len() as u32),
            Literal::Utf8String(str) => Type::StringUtf8(str.len() as u32),
            Literal::Bool(_) => Type::Bool,
            Literal::Int(_) => Type::Int,
            Literal::UInt(_) => Type::UInt,
            Literal::Integer(_) => todo!(),
            Literal::Principal(_) => Type::Principal,
        }
    }
}