use internment::Intern;

use crate::types::{ClarityInteger, RefinedInteger};

#[derive(Debug, Clone)]
pub enum SExpr {
    Error,

    Identifier(String),
    RefinedInteger(RefinedInteger),
    Closure(Vec<Self>),
    Define(Define),
    Op(Op),
    TypeDef(Type),
    Literal(Literal),
    Keyword(Keyword),
    Ctrl(Ctrl)
}

#[derive(Debug, Clone, Copy)]
pub enum Ctrl {
    StartOfContract,
    EndOfContract
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone)]
pub enum Define {
    Map(MapDef),
    DataVar,
    PublicFunction,
    PrivateFunction,
    ReadOnlyFunction
}

#[derive(Debug, Clone)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    DefaultTo(DefaultToDef),
    MapGet,
    Ok,
    MapSet,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int,
    UInt,
    Integer(ClarityInteger),
    AsciiString(String),
    Utf8String(String)
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone)]
pub struct MapDef {
    pub name: String,
    pub key_ty: Type,
    pub val_ty: Type
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub signature: FuncSignature,
    pub body: SExpr
}

#[derive(Debug, Clone)]
pub struct FuncSignature {
    pub name: String,
    pub args: Vec<FuncArg>,
}

#[derive(Debug, Clone)]
pub struct FuncArg {
    pub name: String,
    pub ty: Type
}

#[derive(Debug, Clone)]
pub struct DefaultToDef {
    pub default: Literal,
    pub tail: Box<SExpr>
}