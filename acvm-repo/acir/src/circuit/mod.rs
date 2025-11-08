//! Native structures for representing ACIR

pub mod black_box_functions;
pub mod brillig;
pub mod opcodes;

use crate::{
    circuit::opcodes::display_opcode,
    native_types::{Expression, Witness},
    serialization::{deserialize_any_format, serialize_with_format_from_env},
};
use acir_field::AcirField;
pub use opcodes::Opcode;
use thiserror::Error;
use num_bigint::BigInt;


 use serde_json::Value;
 use core::num;
use std::{collections::HashMap, fs::File, io::prelude::*, iter::FromFn, num::ParseIntError, str::FromStr};

use base64::Engine;
use flate2::Compression;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error as DeserializationError};

use std::collections::BTreeSet;

use self::{brillig::BrilligBytecode, opcodes::BlockId};

/// Specifies the maximum width of the expressions which will be constrained.
///
/// Unbounded Expressions are useful if you are eventually going to pass the ACIR
/// into a proving system which supports R1CS.
///
/// Bounded Expressions are useful if you are eventually going to pass the ACIR
/// into a proving system which supports PLONK, where arithmetic expressions have a
/// finite fan-in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub enum ExpressionWidth {
    #[default]
    Unbounded,
    Bounded {
        width: usize,
    },
}

/// A program represented by multiple ACIR [circuit][Circuit]'s. The execution trace of these
/// circuits is dictated by construction of the [crate::native_types::WitnessStack].
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Default, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub struct Program<F: AcirField> {
    pub functions: Vec<Circuit<F>>,
    pub unconstrained_functions: Vec<BrilligBytecode<F>>,
}

impl<F: AcirField + Serialize + From<String> > Program<F> {
    pub fn write_program_to_json(&self, path: &str) -> std::io::Result<()> {
        let mut file = File::create(path)?;

        let mut functions_json = vec![];
        
        let minusone = F::modulus();
        //let p = F::
        let minusone = minusone.to_string();
        let big_int = BigInt::from_str(minusone.as_str()).expect("Invalid number");

        let prime : BigInt = big_int;

        let mut num_functions = 0;
        for function in &self.functions {
            let function_json = Circuit::write_assert_zero_constraints(function)?;
            functions_json.push(function_json);
            num_functions += 1;
        }

        let json_output = serde_json::json!({
            "functions": functions_json,
            "prime": prime.to_string(),
            "num_functions": num_functions,
        });

        writeln!(file, "{}", serde_json::to_string_pretty(&json_output)?)?;
        file.flush()?;
        file.sync_all()?;
        Ok(())
    }

    pub fn transform_to_r1cs(&mut self) -> std::io::Result<()> {
        let mut new_id = HashMap::new();
        let mut new_witness_index = self.functions.get(0).unwrap().current_witness_index;
        for function in self.functions.iter_mut() {
            function.current_witness_index = new_witness_index;
            new_witness_index = function.transform_to_r1cs(&mut new_id)?;
        }
        Ok(())
    }

    pub fn read_program_from_json(&mut self, path: &str) -> Result<(),std::io::Error> {
        let file = File::open(path)?;
        let json_output: Value = serde_json::from_reader(file)?;

        let mut new_functions= Vec::new();
        let mut i = 0;
        for  circuit_json in json_output["functions"].as_array().unwrap() {

            let mut circuit = self.functions.get(i).unwrap().clone();
            circuit.read_assert_zero_constraints(circuit_json)?;
            new_functions.push(circuit);
            i += 1;
        }
        self.functions = new_functions;
        Ok(())
    }
}


/// Representation of a single ACIR circuit. The execution trace of this structure
/// is dictated by the construction of a [crate::native_types::WitnessMap]
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize, Default, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub struct Circuit<F: AcirField> {
    /// Name of the function represented by this circuit.
    #[serde(default)] // For backwards compatibility
    pub function_name: String,
    /// current_witness_index is the highest witness index in the circuit. The next witness to be added to this circuit
    /// will take on this value. (The value is cached here as an optimization.)
    pub current_witness_index: u32,
    /// The circuit opcodes representing the relationship between witness values.
    ///
    /// The opcodes should be further converted into a backend-specific circuit representation.
    /// When initial witness inputs are provided, these opcodes can also be used for generating an execution trace.
    pub opcodes: Vec<Opcode<F>>,

    /// The set of private inputs to the circuit.
    pub private_parameters: BTreeSet<Witness>,
    // ACIR distinguishes between the public inputs which are provided externally or calculated within the circuit and returned.
    // The elements of these sets may not be mutually exclusive, i.e. a parameter may be returned from the circuit.
    // All public inputs (parameters and return values) must be provided to the verifier at verification time.
    /// The set of public inputs provided by the prover.
    pub public_parameters: PublicInputs,
    /// The set of public inputs calculated within the circuit.
    pub return_values: PublicInputs,
    /// Maps opcode locations to failed assertion payloads.
    /// The data in the payload is embedded in the circuit to provide useful feedback to users
    /// when a constraint in the circuit is not satisfied.
    ///
    // Note: This should be a BTreeMap, but serde-reflect is creating invalid
    // c++ code at the moment when it is, due to OpcodeLocation needing a comparison
    // implementation which is never generated.
    pub assert_messages: Vec<(OpcodeLocation, AssertionPayload<F>)>,
}

/// Enumeration of either an [expression][Expression] or a [memory identifier][BlockId].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub enum ExpressionOrMemory<F> {
    Expression(Expression<F>),
    Memory(BlockId),
}

/// Payload tied to an assertion failure.
/// This data allows users to specify feedback upon a constraint not being satisfied in the circuit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub struct AssertionPayload<F> {
    /// Selector that maps a hash of either a constant string or an internal compiler error type
    /// to an ABI type. The ABI type should then be used to appropriately resolve the payload data.
    pub error_selector: u64,
    /// The dynamic payload data.
    ///
    /// Upon fetching the appropriate ABI type from the `error_selector`, the values
    /// in this payload can be decoded into the given ABI type.
    /// The payload is expected to be empty in the case of a constant string
    /// as the string can be contained entirely within the error type and ABI type.
    pub payload: Vec<ExpressionOrMemory<F>>,
}

/// Value for differentiating error types. Used internally by an [AssertionPayload].
#[derive(Debug, Copy, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct ErrorSelector(u64);

impl ErrorSelector {
    pub fn new(integer: u64) -> Self {
        ErrorSelector(integer)
    }

    pub fn as_u64(&self) -> u64 {
        self.0
    }
}

impl Serialize for ErrorSelector {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.to_string().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ErrorSelector {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s: String = Deserialize::deserialize(deserializer)?;
        let as_u64 = s.parse().map_err(serde::de::Error::custom)?;
        Ok(ErrorSelector(as_u64))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
/// Opcodes are locatable so that callers can
/// map opcodes to debug information related to their context.
pub enum OpcodeLocation {
    Acir(usize),
    // TODO(https://github.com/noir-lang/noir/issues/5792): We can not get rid of this enum field entirely just yet as this format is still
    // used for resolving assert messages which is a breaking serialization change.
    Brillig { acir_index: usize, brillig_index: usize },
}

/// Opcodes are locatable so that callers can
/// map opcodes to debug information related to their context.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct AcirOpcodeLocation(usize);
impl std::fmt::Display for AcirOpcodeLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AcirOpcodeLocation {
    pub fn new(index: usize) -> Self {
        AcirOpcodeLocation(index)
    }
    pub fn index(&self) -> usize {
        self.0
    }
}
/// Index of Brillig opcode within a list of Brillig opcodes.
/// To be used by callers for resolving debug information.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BrilligOpcodeLocation(pub usize);

impl OpcodeLocation {
    // Utility method to allow easily comparing a resolved Brillig location and a debug Brillig location.
    // This method is useful when fetching Brillig debug locations as this does not need an ACIR index,
    // and just need the Brillig index.
    pub fn to_brillig_location(self) -> Option<BrilligOpcodeLocation> {
        match self {
            OpcodeLocation::Brillig { brillig_index, .. } => {
                Some(BrilligOpcodeLocation(brillig_index))
            }
            _ => None,
        }
    }
}

impl std::fmt::Display for OpcodeLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpcodeLocation::Acir(index) => write!(f, "{index}"),
            OpcodeLocation::Brillig { acir_index, brillig_index } => {
                write!(f, "{acir_index}.{brillig_index}")
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum OpcodeLocationFromStrError {
    #[error("Invalid opcode location string: {0}")]
    InvalidOpcodeLocationString(String),
}

/// The implementation of display and FromStr allows serializing and deserializing a OpcodeLocation to a string.
/// This is useful when used as key in a map that has to be serialized to JSON/TOML, for example when mapping an opcode to its metadata.
impl FromStr for OpcodeLocation {
    type Err = OpcodeLocationFromStrError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<_> = s.split('.').collect();

        if parts.is_empty() || parts.len() > 2 {
            return Err(OpcodeLocationFromStrError::InvalidOpcodeLocationString(s.to_string()));
        }

        fn parse_components(parts: Vec<&str>) -> Result<OpcodeLocation, ParseIntError> {
            match parts.len() {
                1 => {
                    let index = parts[0].parse()?;
                    Ok(OpcodeLocation::Acir(index))
                }
                2 => {
                    let acir_index = parts[0].parse()?;
                    let brillig_index = parts[1].parse()?;
                    Ok(OpcodeLocation::Brillig { acir_index, brillig_index })
                }
                _ => unreachable!("`OpcodeLocation` has too many components"),
            }
        }

        parse_components(parts)
            .map_err(|_| OpcodeLocationFromStrError::InvalidOpcodeLocationString(s.to_string()))
    }
}

impl std::fmt::Display for BrilligOpcodeLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let index = self.0;
        write!(f, "{index}")
    }
}

impl<F: AcirField> Circuit<F> {
    pub fn num_vars(&self) -> u32 {
        self.current_witness_index + 1
    }

    /// Returns all witnesses which are required to execute the circuit successfully.
    pub fn circuit_arguments(&self) -> BTreeSet<Witness> {
        self.private_parameters.union(&self.public_parameters.0).cloned().collect()
    }

    /// Returns all public inputs. This includes those provided as parameters to the circuit and those
    /// computed as return values.
    pub fn public_inputs(&self) -> PublicInputs {
        let public_inputs =
            self.public_parameters.0.union(&self.return_values.0).cloned().collect();
        PublicInputs(public_inputs)
    }
}

impl<F: Serialize + AcirField> Program<F> {
    /// Serialize and compress the [Program] into bytes.
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()> {
        let buf = serialize_with_format_from_env(self)?;

        // Compress the data, which should help with formats that uses field names.
        let mut encoder = flate2::write::GzEncoder::new(writer, Compression::default());
        encoder.write_all(&buf)?;
        encoder.finish()?;
        Ok(())
    }

    pub fn serialize_program(program: &Self) -> Vec<u8> {
        let mut program_bytes: Vec<u8> = Vec::new();
        program.write(&mut program_bytes).expect("expected circuit to be serializable");
        program_bytes
    }

    /// Serialize and base64 encode program
    pub fn serialize_program_base64<S>(program: &Self, s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let program_bytes = Program::serialize_program(program);
        let encoded_b64 = base64::engine::general_purpose::STANDARD.encode(program_bytes);
        s.serialize_str(&encoded_b64)
    }
}

impl<F: AcirField + for<'a> Deserialize<'a>> Program<F> {
    /// Decompress and deserialize bytes into a [Program].
    fn read<R: Read>(reader: R) -> std::io::Result<Self> {
        let mut gz_decoder = flate2::read::GzDecoder::new(reader);
        let mut buf = Vec::new();
        gz_decoder.read_to_end(&mut buf)?;
        let program = deserialize_any_format(&buf)?;
        Ok(program)
    }

    /// Deserialize bytecode.
    pub fn deserialize_program(serialized_circuit: &[u8]) -> std::io::Result<Self> {
        Program::read(serialized_circuit)
    }

    /// Deserialize and base64 decode program
    pub fn deserialize_program_base64<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytecode_b64: String = Deserialize::deserialize(deserializer)?;
        let program_bytes = base64::engine::general_purpose::STANDARD
            .decode(bytecode_b64)
            .map_err(D::Error::custom)?;
        let circuit = Self::deserialize_program(&program_bytes).map_err(D::Error::custom)?;
        Ok(circuit)
    }
}

impl<F: AcirField> std::fmt::Display for Circuit<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let write_witness_indices =
            |f: &mut std::fmt::Formatter<'_>, indices: &[u32]| -> Result<(), std::fmt::Error> {
                write!(f, "[")?;
                for (index, witness_index) in indices.iter().enumerate() {
                    write!(f, "w{witness_index}")?;
                    if index != indices.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                writeln!(f, "]")
            };

        write!(f, "private parameters: ")?;
        write_witness_indices(
            f,
            &self
                .private_parameters
                .iter()
                .map(|witness| witness.witness_index())
                .collect::<Vec<_>>(),
        )?;

        write!(f, "public parameters: ")?;
        write_witness_indices(f, &self.public_parameters.indices())?;

        write!(f, "return values: ")?;
        write_witness_indices(f, &self.return_values.indices())?;

        for opcode in &self.opcodes {
            display_opcode(opcode, Some(&self.return_values), f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<F: AcirField> std::fmt::Debug for Circuit<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

impl<F: AcirField> std::fmt::Display for Program<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (func_index, function) in self.functions.iter().enumerate() {
            writeln!(f, "func {func_index}")?;
            writeln!(f, "{function}")?;
        }
        for (func_index, function) in self.unconstrained_functions.iter().enumerate() {
            writeln!(f, "unconstrained func {func_index}: {}", function.function_name)?;
            let width = function.bytecode.len().to_string().len();
            for (index, opcode) in function.bytecode.iter().enumerate() {
                writeln!(f, "{index:>width$}: {opcode}")?;
            }
        }
        Ok(())
    }
}

impl<F: AcirField> std::fmt::Debug for Program<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Default, Hash)]
#[cfg_attr(feature = "arb", derive(proptest_derive::Arbitrary))]
pub struct PublicInputs(pub BTreeSet<Witness>);

impl PublicInputs {
    /// Returns the witness index of each public input
    pub fn indices(&self) -> Vec<u32> {
        self.0.iter().map(|witness| witness.witness_index()).collect()
    }

    pub fn contains(&self, index: usize) -> bool {
        self.0.contains(&Witness(index as u32))
    }
}


impl<F: AcirField + From<String> > Circuit<F> {

    pub fn read_assert_zero_constraints(&mut self, json_output : &Value) -> Result<(), std::io::Error> {

        let inputs: Vec<u32> = serde_json::from_value(json_output["inputs"].clone()).unwrap();
        let outputs: Vec<u32> = serde_json::from_value(json_output["outputs"].clone()).unwrap();
        let constraints: Vec<Value> = serde_json::from_value(json_output["constraints"].clone()).unwrap();
        let number_of_signals: u32 = serde_json::from_value(json_output["number_of_signals"].clone()).unwrap();

        let mut opcodes = Vec::new();
        for constraint in constraints {
            let q_c = F::from(constraint["constant"].as_str().unwrap().to_string());
            let mut mul_terms = Vec::new();
            for mul in constraint["mul"].as_array().unwrap() {
                let coeff = F::from(mul["coeff"].as_str().unwrap().to_string());
                let witness1 = Witness(mul["witness1"].as_u64().unwrap() as u32);
                let witness2 = Witness(mul["witness2"].as_u64().unwrap() as u32);
                mul_terms.push((coeff, witness1, witness2));
            }
            let mut linear_combinations = Vec::new();
            for linear in constraint["linear"].as_array().unwrap() {
                let coeff = F::from(linear["coeff"].as_str().unwrap().to_string());
                let witness = Witness(linear["witness"].as_u64().unwrap() as u32);
                linear_combinations.push((coeff, witness));
            }
            let expr = Expression {
                mul_terms,
                linear_combinations,
                q_c,
            };
            opcodes.push(Opcode::AssertZero(expr));
        }

        

        //let opcodes2 : Vec<Opcode<F>> = self.opcodes.clone().into_iter().filter(|opcode| !matches!(opcode, Opcode::AssertZero(_))).collect();
        let mut new_opcodes = Vec::new();
        let mut index = 0; 
        for opcode in &self.opcodes {
            if let Opcode::AssertZero(_) = opcode {
                new_opcodes.push(opcodes.get(index).unwrap().clone());
                index += 1;
            }
            else {
                new_opcodes.push(opcode.clone());
            }
        }

        /*
        println!("opcodes antes {:?}", self.opcodes.len());
        println!("opcodes antes {:?}", self.opcodes);
        new_opcodes.extend(opcodes2);
        new_opcodes.extend(opcodes);
        println!("opcodes leido {:?}", self.opcodes);*/
        self.opcodes = new_opcodes;
        self.current_witness_index = number_of_signals;
        self.public_parameters = PublicInputs(BTreeSet::from_iter(inputs.into_iter().map(Witness)));
        self.return_values = PublicInputs(BTreeSet::from_iter(outputs.into_iter().map(Witness)));

        Ok(())
    }

    pub fn transform_to_r1cs(&mut self, new_id: &mut HashMap<(Witness, Witness), Witness>) -> std::io::Result<u32> {
        let mut new_opcodes = Vec::new();
        //let mut new_id : HashMap<(Witness, Witness), Witness> = HashMap::new();
        for opcode in &self.opcodes {
            match opcode {
                Opcode::AssertZero(expr) => {
                    if expr.mul_terms.len() <= 1 {
                        new_opcodes.push(opcode.clone());
                    } else {
                        let mut new_linear_combinations = Vec::new();
                        for (coef,witness1,witness2) in expr.mul_terms.clone() {
                            if new_id.contains_key(&(witness1, witness2)) {
                                let new_witness = new_id.get(&(witness1, witness2)).unwrap();
                                new_linear_combinations.push((coef, new_witness.clone()));
                            } else {
                                let new_witness = Witness(self.current_witness_index);
                                self.current_witness_index += 1;
                                new_linear_combinations.push((coef, new_witness));
                                new_id.insert((witness1, witness2), new_witness);
                                let new_mul = Expression {
                                    mul_terms: vec![(F::one(), witness1, witness2)],
                                    linear_combinations: vec![(-F::one(), new_witness)],
                                    q_c: F::zero(),
                                };
                                new_opcodes.push(Opcode::AssertZero(new_mul));
                            }
                        }
                        new_linear_combinations.extend(expr.linear_combinations.clone());
                        let new_expr = Expression {
                            mul_terms: vec![],
                            linear_combinations: new_linear_combinations,
                            q_c: expr.q_c,
                        };
                        new_opcodes.push(Opcode::AssertZero(new_expr));
                    }
                }
                _ => {
                    new_opcodes.push(opcode.clone());
                }
            }
        };

        self.opcodes = new_opcodes;
        Ok(self.current_witness_index)
    }


    pub fn write_assert_zero_constraints(circuit: &Circuit<F>) -> std::io::Result<Value> {
        let mut constraints = vec![];
        let mut inputs = vec![];
        let mut outputs = vec![];
        let mut btree_inputs = BTreeSet::new();
        let mut btree_outputs = BTreeSet::new();
        let mut forbidden_signals = BTreeSet::new();
        for i in &circuit.public_parameters.0 {
            btree_inputs.insert(i.witness_index());
        }
        for i in &circuit.private_parameters {
            btree_inputs.insert(i.witness_index());
        }
        for i in &circuit.return_values.0 {
            btree_outputs.insert(i.witness_index());
        }
        for i in btree_outputs {
           // if !btree_inputs.contains(&i) {
                outputs.push(i);
            //}
        }
        for i in btree_inputs {
            inputs.push(i);
        }

        let mut n_signals = circuit.current_witness_index;

        for opcode in &circuit.opcodes {
            match opcode {
                Opcode::AssertZero(expr) => {
                    let mut constraint = serde_json::json!({
                        "mul": [], 
                        "linear": [],
                        "constant": expr.q_c.to_string(),
                    });

                    for i in &expr.mul_terms {
                        constraint["mul"].as_array_mut().unwrap().push(serde_json::json!({
                        "coeff": i.0.to_string(),
                        "witness1": i.1.witness_index(),
                        "witness2": i.2.witness_index(),
                        }));
                    }
        
                    for i in &expr.linear_combinations {
                        constraint["linear"].as_array_mut().unwrap().push(serde_json::json!({
                        "coeff": i.0.to_string(),
                        "witness": i.1.witness_index(),
                        }));
                    }
        
                    constraints.push(constraint);
                }
                Opcode::BlackBoxFuncCall(black_box_func_call) => {
                    let ipt = black_box_func_call.get_input_witnesses();
                    forbidden_signals.extend(ipt.iter().map(|w| w.witness_index()));
                    let opt = black_box_func_call.get_outputs_vec();
                    forbidden_signals.extend(opt.iter().map(|w| w.witness_index()));
                    
                    let check_range = black_box_func_call.get_range_info();
                    match check_range{
                        Some((witness, num_bits)) =>{
                            if num_bits == 1{
                                println!("Transforming black call {}", black_box_func_call);

                                let wit_squared = serde_json::json!({
                                    "coeff": "1",
                                    "witness1": witness.witness_index(),
                                    "witness2": witness.witness_index(),
                                });
                                let wit = serde_json::json!({
                                    "coeff": (-F::one()).to_string(),
                                    "witness": witness.witness_index(),
                                });
                                
                                let constraint = serde_json::json!({
                                    "mul": [wit_squared], 
                                    "linear": [wit],
                                    "constant": "0",
                                });
                                println!("Adding constraint {}", constraint);
                                constraints.push(constraint);
                            } else{
                                println!("Transforming black call {}", black_box_func_call);

                                // current_witness_index contains the new index
                                let mut constraint_lin = Vec::new();
                                let mut coef = F::one();

                                for i in 0..num_bits{
                                    // adding new aux binary signal and constraint x^2 - x = 0
                                    let new_s = n_signals;

                                    let new_s_squared_c = serde_json::json!({
                                        "coeff": "1",
                                        "witness1": new_s,
                                        "witness2": new_s,
                                    });
                                    let new_s_c = serde_json::json!({
                                        "coeff": (-F::one()).to_string(),
                                        "witness": new_s,
                                    });
                                
                                    let constraint = serde_json::json!({
                                       "mul": [new_s_squared_c], 
                                        "linear": [new_s_c],
                                        "constant": "0",
                                    });
                                    println!("Adding constraint {}", constraint);
                                    constraints.push(constraint);


                                    // adding s to the last linear constraint
                                    let new_s_coef = serde_json::json!({
                                        "coeff": coef.to_string(),
                                        "witness": new_s,
                                    });
                                    constraint_lin.push(new_s_coef);

                                    n_signals += 1;
                                    coef = coef.mul(F::from("2".to_string()));
                                }

                                let wit = serde_json::json!({
                                    "coeff": (-F::one()).to_string(),
                                    "witness": witness.witness_index(),
                                });
                                constraint_lin.push(wit);

                                
                                let last_constraint = serde_json::json!({
                                    "mul": [], 
                                    "linear": constraint_lin,
                                    "constant": "0",
                                });
                                println!("Adding constraint {}", last_constraint);
                                constraints.push(last_constraint);
                            }
                        }
                        None =>{}
                    }
                    
                
                },
                Opcode::MemoryOp {  op, .. } => {
                    for i in op.operation.get_witnesses() { forbidden_signals.insert(i.witness_index());}
                    for i in op.index.get_witnesses() { forbidden_signals.insert(i.witness_index());}
                    for i in op.value.get_witnesses() { forbidden_signals.insert(i.witness_index());}
                    //if predicate.is_some() {
                    //    forbidden_signals.extend(predicate.as_ref().unwrap().get_witnesses().iter().map(|w| w.witness_index()));
                    //}
                },
                Opcode::MemoryInit {  init, .. } => {
                    forbidden_signals.extend(init.iter().map(|w| w.witness_index()));
                },
                Opcode::BrilligCall { inputs, outputs, predicate, id  } => {
                   for i in inputs {
                        match i {
                            brillig::BrilligInputs::Single(expression) => {
                                forbidden_signals.extend(expression.get_witnesses().iter().map(|w| w.witness_index()));
                            },
                            brillig::BrilligInputs::Array(expressions) => {
                                for e in expressions {
                                    forbidden_signals.extend(e.get_witnesses().iter().map(|w| w.witness_index()));
                                }
                            },
                            _ => {},
                        }   
                   }
                   for o in outputs {
                        match o {
                             brillig::BrilligOutputs::Simple(w) => {
                                  forbidden_signals.insert(w.witness_index());
                             },
                             brillig::BrilligOutputs::Array(w) => {
                                forbidden_signals.extend(w.iter().map(|w| w.witness_index()));
                             }
                            }
                    }
                    if predicate.is_some() {
                        forbidden_signals.extend(predicate.as_ref().unwrap().get_witnesses().iter().map(|w| w.witness_index()));
                    }
                },
                Opcode::Call { inputs, outputs, predicate, .. } => {
                    println!("Call opcode found during serialization");
                    forbidden_signals.extend(inputs.iter().map(|w| w.witness_index()));
                    forbidden_signals.extend(outputs.iter().map(|w| w.witness_index()));
                    if predicate.is_some() {
                        forbidden_signals.extend(predicate.as_ref().unwrap().get_witnesses().iter().map(|w| w.witness_index()));
                    }
                },
            }
        };

        let json_output = serde_json::json!({
            "inputs": inputs,
            "outputs": outputs,
            "constraints": constraints,
            "number_of_signals": n_signals
        });
        Ok(json_output)
    }
}

#[cfg(test)]
mod tests {
    use super::{Circuit, Compression};
    use crate::circuit::Program;
    use acir_field::{AcirField, FieldElement};
    use serde::{Deserialize, Serialize};

    #[test]
    fn serialization_roundtrip() {
        let src = "
        private parameters: []
        public parameters: [w2, w12]
        return values: [w4, w12]
        BLACKBOX::AND lhs: w1, rhs: w2, output: w3, bits: 4
        BLACKBOX::RANGE input: w1, bits: 8
        ";
        let circuit = Circuit::from_str(src).unwrap();
        let program = Program { functions: vec![circuit], unconstrained_functions: Vec::new() };

        fn read_write<F: Serialize + for<'a> Deserialize<'a> + AcirField>(
            program: Program<F>,
        ) -> (Program<F>, Program<F>) {
            let bytes = Program::serialize_program(&program);
            let got_program = Program::deserialize_program(&bytes).unwrap();
            (program, got_program)
        }

        let (circ, got_circ) = read_write(program);
        assert_eq!(circ, got_circ);
    }

    #[test]
    fn test_serialize() {
        let src = "
        private parameters: []
        public parameters: [w2]
        return values: [w2]
        ASSERT 0 = 8
        BLACKBOX::RANGE input: w1, bits: 8
        BLACKBOX::AND lhs: w1, rhs: w2, output: w3, bits: 4
        BLACKBOX::KECCAKF1600 inputs: [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25], outputs: [w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50]
        ";
        let circuit = Circuit::from_str(src).unwrap();
        let program = Program { functions: vec![circuit], unconstrained_functions: Vec::new() };

        let json = serde_json::to_string_pretty(&program).unwrap();

        let deserialized = serde_json::from_str(&json).unwrap();
        assert_eq!(program, deserialized);
    }

    #[test]
    fn does_not_panic_on_invalid_circuit() {
        use std::io::Write;

        let bad_circuit = "I'm not an ACIR circuit".as_bytes();

        // We expect to load circuits as compressed artifacts so we compress the junk circuit.
        let mut zipped_bad_circuit = Vec::new();
        let mut encoder =
            flate2::write::GzEncoder::new(&mut zipped_bad_circuit, Compression::default());
        encoder.write_all(bad_circuit).unwrap();
        encoder.finish().unwrap();

        let deserialization_result: Result<Program<FieldElement>, _> =
            Program::deserialize_program(&zipped_bad_circuit);
        assert!(deserialization_result.is_err());
    }

    #[test]
    fn circuit_display_snapshot() {
        let src = "
        private parameters: []
        public parameters: [w2]
        return values: [w2]
        ASSERT 0 = 2*w1 + 8
        BLACKBOX::RANGE input: w1, bits: 8
        BLACKBOX::AND lhs: w1, rhs: w2, output: w3, bits: 4
        BLACKBOX::KECCAKF1600 inputs: [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25], outputs: [w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50]
        ";
        let circuit = Circuit::from_str(src).unwrap();

        // All witnesses are expected to be formatted as `w{witness_index}`.
        insta::assert_snapshot!(
            circuit.to_string(),
            @r"
        private parameters: []
        public parameters: [w2]
        return values: [w2]
        ASSERT 0 = 2*w1 + 8
        BLACKBOX::RANGE input: w1, bits: 8
        BLACKBOX::AND lhs: w1, rhs: w2, output: w3, bits: 4
        BLACKBOX::KECCAKF1600 inputs: [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25], outputs: [w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50]
        "
        );
    }

    /// Property based testing for serialization
    mod props {
        use acir_field::FieldElement;
        use proptest::prelude::*;
        use proptest::test_runner::{TestCaseResult, TestRunner};

        use crate::circuit::Program;
        use crate::native_types::{WitnessMap, WitnessStack};
        use crate::serialization::*;

        // It's not possible to set the maximum size of collections via `ProptestConfig`, only an env var,
        // because e.g. the `VecStrategy` uses `Config::default().max_default_size_range`. On top of that,
        // `Config::default()` reads a static `DEFAULT_CONFIG`, which gets the env vars only once at the
        // beginning, so we can't override this on a test-by-test basis, unless we use `fork`,
        // which is a feature that is currently disabled, because it doesn't work with Wasm.
        // We could add it as a `dev-dependency` just for this crate, but when I tried it just crashed.
        // For now using a const so it's obvious we can't set it to different values for different tests.
        const MAX_SIZE_RANGE: usize = 5;
        const SIZE_RANGE_KEY: &str = "PROPTEST_MAX_DEFAULT_SIZE_RANGE";

        // Define a wrapper around field so we can implement `Arbitrary`.
        // NB there are other methods like `arbitrary_field_elements` around the codebase,
        // but for `proptest_derive::Arbitrary` we need `F: AcirField + Arbitrary`.
        acir_field::field_wrapper!(TestField, FieldElement);

        impl Arbitrary for TestField {
            type Parameters = ();
            type Strategy = BoxedStrategy<Self>;

            fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
                any::<u128>().prop_map(|v| Self(FieldElement::from(v))).boxed()
            }
        }

        /// Override the maximum size of collections created by `proptest`.
        #[allow(unsafe_code)]
        fn run_with_max_size_range<T, F>(cases: u32, f: F)
        where
            T: Arbitrary,
            F: Fn(T) -> TestCaseResult,
        {
            let orig_size_range = std::env::var(SIZE_RANGE_KEY).ok();
            // The defaults are only read once. If they are already set, leave them be.
            if orig_size_range.is_none() {
                unsafe {
                    std::env::set_var(SIZE_RANGE_KEY, MAX_SIZE_RANGE.to_string());
                }
            }

            let mut runner = TestRunner::new(ProptestConfig { cases, ..Default::default() });
            let result = runner.run(&any::<T>(), f);

            // Restore the original.
            unsafe {
                std::env::set_var(SIZE_RANGE_KEY, orig_size_range.unwrap_or_default());
            }

            result.unwrap();
        }

        #[test]
        fn prop_program_proto_roundtrip() {
            run_with_max_size_range(100, |program: Program<TestField>| {
                let bz = proto_serialize(&program);
                let de = proto_deserialize(&bz)?;
                prop_assert_eq!(program, de);
                Ok(())
            });
        }

        #[test]
        fn prop_program_bincode_roundtrip() {
            run_with_max_size_range(100, |program: Program<TestField>| {
                let bz = bincode_serialize(&program)?;
                let de = bincode_deserialize(&bz)?;
                prop_assert_eq!(program, de);
                Ok(())
            });
        }

        #[test]
        fn prop_program_msgpack_roundtrip() {
            run_with_max_size_range(100, |(program, compact): (Program<TestField>, bool)| {
                let bz = msgpack_serialize(&program, compact)?;
                let de = msgpack_deserialize(&bz)?;
                prop_assert_eq!(program, de);
                Ok(())
            });
        }

        #[test]
        fn prop_program_roundtrip() {
            run_with_max_size_range(10, |program: Program<TestField>| {
                let bz = Program::serialize_program(&program);
                let de = Program::deserialize_program(&bz)?;
                prop_assert_eq!(program, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_stack_proto_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessStack<TestField>| {
                let bz = proto_serialize(&witness);
                let de = proto_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_stack_bincode_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessStack<TestField>| {
                let bz = bincode_serialize(&witness)?;
                let de = bincode_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_stack_msgpack_roundtrip() {
            run_with_max_size_range(10, |(witness, compact): (WitnessStack<TestField>, bool)| {
                let bz = msgpack_serialize(&witness, compact)?;
                let de = msgpack_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_stack_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessStack<TestField>| {
                let bz = witness.serialize()?;
                let de = WitnessStack::deserialize(bz.as_slice())?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_map_proto_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessMap<TestField>| {
                let bz = proto_serialize(&witness);
                let de = proto_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_map_bincode_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessMap<TestField>| {
                let bz = bincode_serialize(&witness)?;
                let de = bincode_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_map_msgpack_roundtrip() {
            run_with_max_size_range(10, |(witness, compact): (WitnessMap<TestField>, bool)| {
                let bz = msgpack_serialize(&witness, compact)?;
                let de = msgpack_deserialize(&bz)?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }

        #[test]
        fn prop_witness_map_roundtrip() {
            run_with_max_size_range(10, |witness: WitnessMap<TestField>| {
                let bz = witness.serialize()?;
                let de = WitnessMap::deserialize(bz.as_slice())?;
                prop_assert_eq!(witness, de);
                Ok(())
            });
        }
    }
}
