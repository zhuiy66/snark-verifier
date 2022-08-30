use crate::{
    loader::evm::modulus,
    loader::{EcPointLoader, LoadedEcPoint, LoadedScalar, Loader, ScalarLoader},
    util::{Curve, FieldOps, Itertools, PrimeField, UncompressedEncoding},
};
use ethereum_types::U256;
use std::{
    cell::RefCell,
    fmt::{self, Debug, Display},
    iter,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    process::{Command, Stdio},
    rc::Rc,
};

use super::fe_to_u256;

fn hex_encode_u256(value: &U256) -> String {
    let mut bytes = [0; 32];
    value.to_big_endian(&mut bytes);
    format!("0x{}", hex::encode(bytes))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Constant(U256),
    Variable(usize),
    Memory(usize),
}

impl Value {
    fn mstore(&self, value: String) -> String {
        if let Value::Memory(idx) = self {
            let offset = idx * 0x20;
            format!("mstore(add(mem, {offset:#x}), {value})")
        } else {
            unreachable!()
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Constant(constant) => write!(f, "{}", hex_encode_u256(constant)),
            Value::Variable(idx) => write!(f, "var{idx}"),
            Value::Memory(idx) => {
                let offset = idx * 0x20;
                write!(f, "mload(add(mem, {offset:#x}))")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct EvmLoader {
    base_modulus: U256,
    scalar_modulus: U256,
    first_part: RefCell<Vec<String>>,
    second_part: RefCell<Vec<String>>,
    memc: RefCell<usize>,
    varc: RefCell<usize>,
    #[cfg(test)]
    _gas_metering_ids: RefCell<Vec<String>>,
}

impl EvmLoader {
    pub fn new<Base, Scalar>() -> Rc<Self>
    where
        Base: PrimeField<Repr = [u8; 32]>,
        Scalar: PrimeField<Repr = [u8; 32]>,
    {
        let base_modulus = modulus::<Base>();
        let scalar_modulus = modulus::<Scalar>();
        Rc::new(Self {
            base_modulus,
            scalar_modulus,
            first_part: Default::default(),
            second_part: Default::default(),
            memc: Default::default(),
            varc: Default::default(),
            #[cfg(test)]
            _gas_metering_ids: RefCell::new(Vec::new()),
        })
    }

    pub fn deployment_code(self: &Rc<Self>) -> Vec<u8> {
        vec![]
    }

    pub fn code(self: &Rc<Self>) -> Vec<u8> {
        let mut cmd = Command::new("solc");

        let mut child = cmd
            .arg("--ir-optimized")
            .arg("--optimize")
            .arg("-")
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();

        use std::io::Write;
        let code = format!(
            "
// SPDX-License-Identifier: MIT

pragma solidity 0.8.16;

contract Verifier {{
    fallback() external {{
        uint256[{}] memory mem;

        assembly {{
            let success := true
            let freePtr
            
            {{
                let fp := {}
                let fr := {}

                let transcriptState
                let tmp1
                let tmp2

{}
            }}

{}

            if not(success) {{ revert(0, 0) }}
       }}
    }}
}}
            ",
            *self.memc.borrow(),
            hex_encode_u256(&self.base_modulus),
            hex_encode_u256(&self.scalar_modulus),
            self.first_part
                .borrow()
                .iter()
                .map(|line| format!("                {}\n", line))
                .reduce(|acc, line| acc + &line)
                .unwrap(),
            self.second_part
                .borrow()
                .iter()
                .map(|line| format!("            {}\n", line))
                .reduce(|acc, line| acc + &line)
                .unwrap(),
        );
        let mut file = std::fs::File::create("./V.sol").unwrap();
        write!(&mut file, "{}", code).unwrap();
        write!(child.stdin.take().unwrap(), "{}", code).unwrap();

        fn decode_hex(s: &String) -> Vec<u8> {
            (0..s.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
                .collect()
        }

        let output =
            String::from_utf8(cmd.output().expect("failed to execute process").stdout).unwrap();
        decode_hex(&output)
    }

    fn var(self: &Rc<Self>) -> Value {
        let var = *self.varc.borrow();
        *self.varc.borrow_mut() += 1;
        Value::Variable(var)
    }

    fn mem(self: &Rc<Self>) -> Value {
        let mem = *self.memc.borrow();
        *self.memc.borrow_mut() += 1;
        Value::Memory(mem)
    }

    fn scalar(self: &Rc<Self>, value: Value) -> Scalar {
        Scalar {
            loader: self.clone(),
            value,
        }
    }

    fn ec_point(self: &Rc<Self>, x: Value, y: Value) -> EcPoint {
        EcPoint {
            loader: self.clone(),
            x,
            y,
        }
    }

    pub fn calldataload_scalar(self: &Rc<Self>, offset: usize) -> Scalar {
        let scalar = self.scalar(self.mem());
        self.first_part.borrow_mut().push(
            scalar
                .value
                .mstore(format!("mod(calldataload({offset:#x}), fr)")),
        );
        scalar
    }

    pub fn calldataload_ec_point(self: &Rc<Self>, offset: usize) -> EcPoint {
        let mut ec_point = self.ec_point(self.var(), self.var());
        self.first_part.borrow_mut().extend(
            [(ec_point.x(), offset), (ec_point.y(), offset + 0x20)]
                .map(|(value, offset)| format!("let {value} := calldataload({offset:#x})")),
        );
        self.validate_ec_point(&mut ec_point);
        ec_point
    }

    pub fn calldataload_ec_point_from_limbs<const LIMBS: usize, const BITS: usize>(
        self: &Rc<Self>,
        offset: usize,
    ) -> EcPoint {
        let mut ec_point = self.ec_point(self.var(), self.var());
        self.first_part.borrow_mut().extend(
            [
                (ec_point.x(), offset),
                (ec_point.y(), offset + 0x20 * LIMBS),
            ]
            .into_iter()
            .flat_map(|(value, offset)| {
                iter::once(format!("let {value} := calldataload({offset:#x})")).chain(
                    (offset..)
                        .step_by(0x20)
                        .zip((0..).step_by(BITS))
                        .skip(1)
                        .map(move |(offset, shift)| {
                            format!(
                                "{value} := add({value}, shl({shift}, calldataload({offset:#x})))"
                            )
                        })
                        .take(3),
                )
            }),
        );
        self.validate_ec_point(&mut ec_point);
        ec_point
    }

    fn validate_ec_point(self: &Rc<Self>, ec_point: &mut EcPoint) {
        let x = ec_point.x();
        let y = ec_point.y();
        ec_point.x = self.mem();
        ec_point.y = self.mem();
        self.first_part.borrow_mut().extend([
            format!("success := and(success, lt({x}, fp))"),
            format!("success := and(success, lt({y}, fp))"),
            format!("success := and(success, not(or(iszero({x}), iszero({y}))))"),
            format!("let {y}Square := mulmod({y}, {y}, fp)"),
            format!("let {x}CubicPlus3 := addmod(mulmod(mulmod({x}, {x}, fp), {x}, fp), 3, fp)"),
            format!("success := and(success, eq({y}Square, {x}CubicPlus3))"),
            ec_point.x.mstore(format!("{}", x)),
            ec_point.y.mstore(format!("{}", y)),
        ]);
    }

    pub fn set_transcript_state(self: &Rc<Self>, transcript_state: Value) {
        self.first_part
            .borrow_mut()
            .push(format!("transcriptState := {transcript_state}"))
    }

    pub fn squeeze_challenge(self: &Rc<Self>, inputs: Vec<Value>) -> Scalar {
        let challenge = self.scalar(self.mem());
        let input_bytes = 0x20
            + if inputs.is_empty() {
                1
            } else {
                inputs.len() * 0x20
            };
        self.first_part.borrow_mut().extend(
            iter::empty()
                .chain(
                    ["freePtr := mload(0x40)", "mstore(freePtr, transcriptState)"]
                        .into_iter()
                        .map_into(),
                )
                .chain(
                    (0x20..)
                        .step_by(0x20)
                        .zip(inputs.iter())
                        .map(|(offset, input)| {
                            format!("mstore(add(freePtr, {offset:#x}), {input})")
                        }),
                )
                .chain(
                    inputs
                        .is_empty()
                        .then(|| "mstore8(add(freePtr, 0x20), 0x01)".into()),
                )
                .chain([
                    format!("transcriptState := keccak256(freePtr, {input_bytes:#x})"),
                    challenge
                        .value
                        .mstore("mod(transcriptState, fp)".to_string()),
                ]),
        );
        challenge
    }

    fn ec_point_add(self: &Rc<Self>, _: &EcPoint, _: &EcPoint) -> EcPoint {
        unreachable!()
    }

    fn ec_point_sub(self: &Rc<Self>, _: &EcPoint, _: &EcPoint) -> EcPoint {
        unreachable!()
    }

    fn ec_point_neg(self: &Rc<Self>, _: &EcPoint) -> EcPoint {
        unreachable!()
    }

    pub fn pairing(
        self: &Rc<Self>,
        lhs: &EcPoint,
        g2: (U256, U256, U256, U256),
        rhs: &EcPoint,
        minus_s_g2: (U256, U256, U256, U256),
    ) {
        self.second_part.borrow_mut().extend(
            iter::empty()
                .chain(Some("freePtr := mload(0x40)".to_string()))
                .chain(
                    (0..)
                        .step_by(0x20)
                        .zip(
                            iter::empty()
                                .chain([lhs.x(), lhs.y()].map(|value| value.to_string()))
                                .chain([&g2.0, &g2.1, &g2.2, &g2.3].map(hex_encode_u256))
                                .chain([rhs.x(), rhs.y()].map(|value| value.to_string()))
                                .chain(
                                    [&minus_s_g2.0, &minus_s_g2.1, &minus_s_g2.2, &minus_s_g2.3]
                                        .map(hex_encode_u256),
                                ),
                        )
                        .map(|(offset, value)| {
                            format!("mstore(add(freePtr, {offset:#x}), {value})")
                        }),
                )
                .chain(
                    [
                        "success := and(success, staticcall(gas(), 8, freePtr, 0x180, 0x00, 0x20))",
                        "success := and(success, mload(0x00))",
                    ]
                    .into_iter()
                    .map_into(),
                ),
        );
    }

    fn add(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        let output = self.scalar(self.mem());
        self.first_part
            .borrow_mut()
            .push(output.value.mstore(format!("addmod({lhs}, {rhs}, fr)")));
        output
    }

    fn sub(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        let output = self.scalar(self.mem());
        self.first_part.borrow_mut().push(
            output
                .value
                .mstore(format!("addmod({lhs}, sub(fr, {rhs}), fr)")),
        );
        output
    }

    fn mul(self: &Rc<Self>, lhs: &Scalar, rhs: &Scalar) -> Scalar {
        match (lhs.value, rhs.value) {
            (Value::Constant(U256([1, 0, 0, 0])), value)
            | (value, Value::Constant(U256([1, 0, 0, 0]))) => self.scalar(value),
            _ => {
                let output = self.scalar(self.mem());
                self.first_part
                    .borrow_mut()
                    .push(output.value.mstore(format!("mulmod({lhs}, {rhs}, fr)")));
                output
            }
        }
    }

    fn neg(self: &Rc<Self>, scalar: &Scalar) -> Scalar {
        let output = self.scalar(self.mem());
        self.first_part
            .borrow_mut()
            .push(output.value.mstore(format!("sub(fr, {scalar})")));
        output
    }
}

#[cfg(test)]
impl EvmLoader {
    fn start_gas_metering(self: &Rc<Self>, _identifier: &str) {
        todo!()
        // self._gas_metering_ids
        //     .borrow_mut()
        //     .push(identifier.to_string());
        // self.first_part.borrow_mut().gas().swap(1);
    }

    fn end_gas_metering(self: &Rc<Self>) {
        todo!()
        // self.first_part
        //     .borrow_mut()
        //     .swap(1)
        //     .push(9)
        //     .gas()
        //     .swap(2)
        //     .sub()
        //     .sub()
        //     .push(0)
        //     .push(0)
        //     .log1();
    }

    pub fn print_gas_metering(self: &Rc<Self>, _costs: Vec<u64>) {
        todo!()
        // for (identifier, cost) in self._gas_metering_ids.borrow().iter().zip(costs) {
        //     println!("{}: {}", identifier, cost);
        // }
    }
}

#[derive(Clone)]
pub struct EcPoint {
    loader: Rc<EvmLoader>,
    x: Value,
    y: Value,
}

impl EcPoint {
    pub(super) fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    pub fn x(&self) -> Value {
        self.x
    }

    pub fn y(&self) -> Value {
        self.y
    }
}

impl Debug for EcPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcPoint")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}

impl Add for EcPoint {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.loader.ec_point_add(&self, &rhs)
    }
}

impl Sub for EcPoint {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.loader.ec_point_sub(&self, &rhs)
    }
}

impl Neg for EcPoint {
    type Output = Self;

    fn neg(self) -> Self {
        self.loader.ec_point_neg(&self)
    }
}

impl<'a> Add<&'a Self> for EcPoint {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self {
        self.loader.ec_point_add(&self, rhs)
    }
}

impl<'a> Sub<&'a Self> for EcPoint {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self {
        self.loader.ec_point_sub(&self, rhs)
    }
}

impl AddAssign for EcPoint {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.loader.ec_point_add(self, &rhs);
    }
}

impl SubAssign for EcPoint {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.loader.ec_point_sub(self, &rhs);
    }
}

impl<'a> AddAssign<&'a Self> for EcPoint {
    fn add_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.ec_point_add(self, rhs);
    }
}

impl<'a> SubAssign<&'a Self> for EcPoint {
    fn sub_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.ec_point_sub(self, rhs);
    }
}

impl PartialEq for EcPoint {
    fn eq(&self, other: &Self) -> bool {
        (self.x, self.y) == (other.x, other.y)
    }
}

impl<C> LoadedEcPoint<C> for EcPoint
where
    C: Curve + UncompressedEncoding<Uncompressed = [u8; 0x40]>,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    type Loader = Rc<EvmLoader>;

    fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    fn multi_scalar_multiplication(pairs: impl IntoIterator<Item = (Scalar, EcPoint)>) -> Self {
        let (non_scaled, scaled) = pairs.into_iter().fold(
            (Vec::new(), Vec::new()),
            |(mut non_scaled, mut scaled), (mut scalar, ec_point)| {
                if matches!(scalar.value, Value::Constant(U256([1, 0, 0, 0]))) {
                    non_scaled.push(ec_point);
                } else {
                    if let value @ Value::Variable(_) = scalar.value {
                        scalar = scalar.loader.scalar(scalar.loader.mem());
                        scalar
                            .loader
                            .first_part
                            .borrow_mut()
                            .push(scalar.value.mstore(format!("{}", value)));
                    }
                    scaled.push((ec_point, scalar))
                }
                (non_scaled, scaled)
            },
        );
        let loader = &non_scaled.first().unwrap().loader;

        let output = loader.ec_point(loader.mem(), loader.mem());
        loader.second_part.borrow_mut().extend(
            iter::empty()
                .chain(Some("freePtr := mload(0x40)".to_string()))
                .chain(
                    non_scaled.first().map(|ec_point| {
                        let x = ec_point.x();
                        let y = ec_point.y();
                        vec![
                            format!("mstore(freePtr, {x})"),
                            format!("mstore(add(freePtr, 0x20), {y})"),
                        ]
                    }).into_iter().chain(

                        non_scaled.iter().skip(1).map(|ec_point| {
                            let x = ec_point.x();
                            let y = ec_point.y();
                            vec![
                                format!("mstore(add(freePtr, 0x40), {x})"),
                                format!("mstore(add(freePtr, 0x60), {y})"),
                                "success := and(success, staticcall(gas(), 6, freePtr, 0x80, freePtr, 0x40))".to_string()
                            ]
                        })
                    ).chain(
                        scaled.iter().skip(1).map(|(ec_point, scalar)| {
                            let x = ec_point.x();
                            let y = ec_point.y();
                            vec![
                                format!("mstore(add(freePtr, 0x40), {x})"),
                                format!("mstore(add(freePtr, 0x60), {y})"),
                                format!("mstore(add(freePtr, 0x80), {scalar})"),
                                "success := and(success, staticcall(gas(), 7, add(freePtr, 0x40), 0x60, add(freePtr, 0x40), 0x40))".to_string(),
                                "success := and(success, staticcall(gas(), 6, freePtr, 0x80, freePtr, 0x40))".to_string()
                            ]
                        })
                    ).flatten()
                ).chain(
                    [
                        output.x.mstore("mload(freePtr)".to_string()),
                        output.y.mstore("mload(add(freePtr, 0x20))".to_string()),
                    ]
                ),

        );
        output
    }
}

#[derive(Clone)]
pub struct Scalar {
    loader: Rc<EvmLoader>,
    value: Value,
}

impl Scalar {
    pub fn value(&self) -> Value {
        self.value
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scalar")
            .field("value", &self.value)
            .finish()
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl Add for Scalar {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.loader.add(&self, &rhs)
    }
}

impl Sub for Scalar {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self.loader.sub(&self, &rhs)
    }
}

impl Mul for Scalar {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        self.loader.mul(&self, &rhs)
    }
}

impl Neg for Scalar {
    type Output = Self;

    fn neg(self) -> Self {
        self.loader.neg(&self)
    }
}

impl<'a> Add<&'a Self> for Scalar {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self {
        self.loader.add(&self, rhs)
    }
}

impl<'a> Sub<&'a Self> for Scalar {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self {
        self.loader.sub(&self, rhs)
    }
}

impl<'a> Mul<&'a Self> for Scalar {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self {
        self.loader.mul(&self, rhs)
    }
}

impl AddAssign for Scalar {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.loader.add(self, &rhs);
    }
}

impl SubAssign for Scalar {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.loader.sub(self, &rhs);
    }
}

impl MulAssign for Scalar {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.loader.mul(self, &rhs);
    }
}

impl<'a> AddAssign<&'a Self> for Scalar {
    fn add_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.add(self, rhs);
    }
}

impl<'a> SubAssign<&'a Self> for Scalar {
    fn sub_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.sub(self, rhs);
    }
}

impl<'a> MulAssign<&'a Self> for Scalar {
    fn mul_assign(&mut self, rhs: &'a Self) {
        *self = self.loader.mul(self, rhs);
    }
}

impl FieldOps for Scalar {
    fn invert(&self) -> Option<Scalar> {
        unimplemented!()
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<F: PrimeField<Repr = [u8; 0x20]>> LoadedScalar<F> for Scalar {
    type Loader = Rc<EvmLoader>;

    fn loader(&self) -> &Rc<EvmLoader> {
        &self.loader
    }

    fn batch_invert<'a>(values: impl IntoIterator<Item = &'a mut Self>) {
        let values = values.into_iter().collect_vec();
        let loader = &values.first().unwrap().loader;

        let products = iter::repeat_with(|| loader.scalar(loader.var()))
            .take(values.len() - 1)
            .collect_vec();
        loader.first_part.borrow_mut().extend(
            iter::empty()
                .chain({
                    let first = products.first().unwrap();
                    let lhs = &values[0];
                    let rhs = &values[1];
                    Some(format!("let {first} := mulmod({lhs}, {rhs}, fr)"))
                })
                .chain(
                    products
                        .iter()
                        .zip(products.iter().skip(1))
                        .zip(values.iter().skip(2))
                        .map(|((curr, next), value)| {
                            format!("let {next} := mulmod({curr}, {value}, fr)")
                        }),
                )
                .chain({
                    let last = products.last().unwrap();
                    [
                        "freePtr := mload(0x40)",
                        "mstore(freePtr, 0x20)",
                        "mstore(add(freePtr, 0x20), 0x20)",
                        "mstore(add(freePtr, 0x40), 0x20)",
                        &format!("mstore(add(freePtr, 0x60), {last})"),
                        "mstore(add(freePtr, 0x80), sub(fr, 2))",
                        "mstore(add(freePtr, 0xa0), fr)",
                        "success := and(success, staticcall(gas(), 0x05, freePtr, 0xc0, 0x00, 0x20))",
                        "tmp1 := mload(0x00)",
                    ].into_iter().map_into()
                })
                .chain(
                    products
                        .iter().rev()
                        .zip(values.iter())
                        .flat_map(|(product, value)| {
                            [
                                format!("tmp2 := mulmod(tmp1, {value}, fr)"),
                                value.value.mstore(format!("mulmod(tmp1, {product}, fr)"))
                                ,
                                "tmp1 := tmp2".to_string()
                            ]
                        }).chain({
                            Some(values[0].value.mstore("tmp1".to_string()))
                        }),
                ),
        );
    }
}

impl<C> EcPointLoader<C> for Rc<EvmLoader>
where
    C: Curve + UncompressedEncoding<Uncompressed = [u8; 0x40]>,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    type LoadedEcPoint = EcPoint;

    fn ec_point_load_const(&self, value: &C) -> EcPoint {
        let bytes = value.to_uncompressed();
        let (x, y) = (
            U256::from_little_endian(&bytes[..32]),
            U256::from_little_endian(&bytes[32..]),
        );
        self.ec_point(Value::Constant(x), Value::Constant(y))
    }
}

impl<F: PrimeField<Repr = [u8; 0x20]>> ScalarLoader<F> for Rc<EvmLoader> {
    type LoadedScalar = Scalar;

    fn load_const(&self, value: &F) -> Scalar {
        self.scalar(Value::Constant(fe_to_u256(*value)))
    }
}

impl<C> Loader<C> for Rc<EvmLoader>
where
    C: Curve + UncompressedEncoding<Uncompressed = [u8; 0x40]>,
    C::Scalar: PrimeField<Repr = [u8; 0x20]>,
{
    #[cfg(test)]
    fn start_cost_metering(&self, identifier: &str) {
        self.start_gas_metering(identifier)
    }

    #[cfg(test)]
    fn end_cost_metering(&self) {
        self.end_gas_metering()
    }
}
