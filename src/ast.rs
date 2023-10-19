use crate::types::{ClarityInteger, RefinedInteger};

#[derive(Debug, Clone, PartialEq)]
pub enum SExpr {
    Error,

    Identifier(Box<Identifier>),
    RefinedInteger(RefinedInteger),
    Closure(Vec<Self>),
    Define(Define),
    Op(Op),
    TypeDef(Type),
    Literal(Literal),
    Keyword(Keyword),
    Tuple(Vec<ArgDef>)
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum Define {
    Map(MapDef),
    DataVar,
    PublicFunction(Box<FuncDef>),
    PrivateFunction(Box<FuncDef>),
    ReadOnlyFunction(Box<FuncDef>),
    Tuple(TupleDef),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    DefaultTo(DefaultToDef),
    MapGet,
    Ok(Box<SExpr>),
    Err(Box<SExpr>),
    MapSet,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int,
    UInt,
    Integer(ClarityInteger),
    AsciiString(String),
    Utf8String(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    UInt,
    Bool,
    Principal,
    Buff,
    StringAscii(u32),
    StringUtf8(u32),
    List,
    Optional,
    Response,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Identifier {
    String(String),
    Expr(SExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MapDef {
    pub name: String,
    pub key_ty: Box<SExpr>,
    pub val_ty: Box<SExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef {
    pub signature: FuncSignature,
    pub body: SExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FuncKind {
    Public,
    Private,
    ReadOnly,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncSignature {
    pub name: String,
    pub args: Vec<ArgDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArgDef {
    pub name: String,
    pub ty: SExpr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DefaultToDef {
    pub default: Box<SExpr>,
    pub tail: Box<SExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleDef {
    pub name: String,
    pub args: Vec<ArgDef>,
}
