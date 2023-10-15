use crate::types::{ClarityType, FunctionKind};

#[derive(Debug)]
pub struct MapSignature {
    pub name: String,
    pub key_ty: ClarityType,
    pub val_ty: ClarityType
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub kind: FunctionKind,
    pub name: String,
    pub params: Vec<ClarityType>,
    pub returns: ClarityType
}