import {
  computeDAGLayout,
  useCanvasState,
  useHostTheme,
  useMemo,
  useState,
  Callout,
  Code,
  Divider,
  Grid,
  H1,
  H3,
  Pill,
  Row,
  Select,
  Stack,
  Stat,
  Text,
  TextInput,
  Toggle,
} from "cursor/canvas";
import type { CanvasHostTheme } from "cursor/canvas";

// n: [crate, type, trait, function, flags, R1CS-SOUND-IF, R1CS-COMPLETE-IF, file:line]
// flags: FUN-SPEC, R1CS-SPEC, PFCS-SPEC, R1CS-SAMPLES, R1CS-SOUND, R1CS-COMPLETE ("x" = excluded)
// e: [caller, callee]; d: [dispatch name, candidate impls]; de: [caller, dispatch]
type RawNode = [string, string, string, string, string, string, string, string];
type Raw = { n: RawNode[]; e: [number, number][]; d: [string, number[]][]; de: [number, number][] };
// BEGIN GENERATED DATA by aleovm_circuit_call_graph.py; do not edit by hand.
const DATA: Raw = {
  n: [
    ["account","ComputeKey","","from_private_key","100000","","","account/src/compute_key/from_private_key.rs:20"],
    ["account","ComputeKey","","to_address","110011","Group::new on pk_sig and pr_sig (points on the curve); allocated wires bound","sk_prf bits/range witnesses and canonical fold-step witnesses, whose constraints mention only bound wires","account/src/compute_key/to_address.rs:20"],
    ["account","ComputeKey","Equal","is_equal","110111","Literal::new signature arm on the signature holding each compute key (pk_sig, pr_sig in the group; sk_prf a scalar)","","account/src/compute_key/equal.rs:24"],
    ["account","ComputeKey","Equal","is_not_equal","110111","Literal::new signature arm on the signature holding each compute key (pk_sig, pr_sig in the group; sk_prf a scalar)","","account/src/compute_key/equal.rs:42"],
    ["account","ComputeKey","From","from","110111","Group::new on pk_sig and pr_sig (points on the curve)","","account/src/compute_key/from.rs:20"],
    ["account","ComputeKey","FromBits","from_bits_be","100000","","","account/src/compute_key/helpers/from_bits.rs:39"],
    ["account","ComputeKey","FromBits","from_bits_le","100000","","","account/src/compute_key/helpers/from_bits.rs:22"],
    ["account","ComputeKey","Inject","new","110011","","","account/src/compute_key/mod.rs:44"],
    ["account","ComputeKey","Ternary","ternary","111111","Boolean::new on the condition; both operands are compute keys from prior circuits (pk_sig, pr_sig on the curve, sk_prf a scalar) whose wires carry their coordinates (crv-compute-key-ternary-gadget-sound)","","account/src/compute_key/ternary.rs:23"],
    ["account","ComputeKey","ToBits","write_bits_be","100000","","","account/src/compute_key/helpers/to_bits.rs:27"],
    ["account","ComputeKey","ToBits","write_bits_le","100000","","","account/src/compute_key/helpers/to_bits.rs:22"],
    ["account","ComputeKey","ToFields","to_fields","111111","","","account/src/compute_key/helpers/to_fields.rs:22"],
    ["account","PrivateKey","","to_compute_key","100000","","","account/src/private_key/to_compute_key.rs:20"],
    ["account","PrivateKey","","to_view_key","100000","","","account/src/private_key/to_view_key.rs:20"],
    ["account","Signature","","verify","110010","Group::new on pk_sig, pr_sig and the address (points on the curve); allocated wires bound; the hash's placeholder wire unbound","","account/src/signature/verify.rs:20"],
    ["account","Signature","Equal","is_equal","110011","Literal::new signature arm on each operand (literal-signature-new-sound-unconditional: challenge, response, sk_prf scalars; pk_sig, pr_sig in the group)","","account/src/signature/equal.rs:24"],
    ["account","Signature","Equal","is_not_equal","110011","Literal::new signature arm on each operand (literal-signature-new-sound-unconditional: challenge, response, sk_prf scalars; pk_sig, pr_sig in the group)","","account/src/signature/equal.rs:42"],
    ["account","Signature","FromBits","from_bits_be","100000","","","account/src/signature/helpers/from_bits.rs:48"],
    ["account","Signature","FromBits","from_bits_le","100000","","","account/src/signature/helpers/from_bits.rs:22"],
    ["account","Signature","Inject","new","110011","","","account/src/signature/mod.rs:42"],
    ["account","Signature","Ternary","ternary","111111","Boolean::new on the condition; Literal::new signature arm on each operand (literal-signature-new-sound-unconditional: challenge, response, sk_prf scalars; pk_sig, pr_sig in the group)","","account/src/signature/ternary.rs:23"],
    ["account","Signature","ToBits","write_bits_be","110011","Literal::new signature arm on the input (challenge and response scalars; pk_sig, pr_sig in the group); public unit wire 1","","account/src/signature/helpers/to_bits.rs:27"],
    ["account","Signature","ToBits","write_bits_le","110011","Literal::new signature arm on the input (challenge and response scalars; pk_sig, pr_sig in the group); public unit wire 1","","account/src/signature/helpers/to_bits.rs:22"],
    ["account","Signature","ToFields","to_fields","111111","","","account/src/signature/helpers/to_fields.rs:22"],
    ["account","ViewKey","","from_private_key","100000","","","account/src/view_key/from_private_key.rs:20"],
    ["account","ViewKey","","to_address","110011","","view key bits/range witnesses and canonical fold-step witnesses","account/src/view_key/to_address.rs:20"],
    ["algorithms","BHP","Commit","commit","110011","Boolean::new on each input bit","","algorithms/src/bhp/commit.rs:24"],
    ["algorithms","BHP","CommitUncompressed","commit_uncompressed","110011","Boolean::new on each input bit","","algorithms/src/bhp/commit_uncompressed.rs:26"],
    ["algorithms","BHP","HashUncompressed","hash_uncompressed","110011","Boolean::new on each input bit","","algorithms/src/bhp/hash_uncompressed.rs:28"],
    ["algorithms","BHPHasher","HashUncompressed","hash_uncompressed","110011","Boolean::new on each input bit","","algorithms/src/bhp/hasher/hash_uncompressed.rs:30"],
    ["algorithms","BHPHasher","Inject","new","x00000","","","algorithms/src/bhp/hasher/mod.rs:63"],
    ["algorithms","Elligator2","","encode","110011","","","algorithms/src/elligator2/encode.rs:21"],
    ["algorithms","Keccak","","pad_keccak","110011","","","algorithms/src/keccak/hash.rs:92"],
    ["algorithms","Keccak","","pad_sha3","110011","","","algorithms/src/keccak/hash.rs:122"],
    ["algorithms","Keccak","","permutation_f","110011","","","algorithms/src/keccak/hash.rs:156"],
    ["algorithms","Keccak","","rotate_left","110011","","","algorithms/src/keccak/hash.rs:276"],
    ["algorithms","Keccak","","round","110011","","","algorithms/src/keccak/hash.rs:185"],
    ["algorithms","Pedersen","Commit","commit","110011","Boolean::new on each input bit","","algorithms/src/pedersen/commit.rs:24"],
    ["algorithms","Pedersen","CommitUncompressed","commit_uncompressed","110011","Boolean::new on each input bit","","algorithms/src/pedersen/commit_uncompressed.rs:24"],
    ["algorithms","Pedersen","HashUncompressed","hash_uncompressed","110011","Boolean::new on each input bit","","algorithms/src/pedersen/hash_uncompressed.rs:25"],
    ["algorithms","Poseidon","","absorb","110011","","","algorithms/src/poseidon/hash_many.rs:45"],
    ["algorithms","Poseidon","","apply_ark","110011","","","algorithms/src/poseidon/hash_many.rs:145"],
    ["algorithms","Poseidon","","apply_mds","110011","","","algorithms/src/poseidon/hash_many.rs:167"],
    ["algorithms","Poseidon","","apply_s_box","110011","","","algorithms/src/poseidon/hash_many.rs:153"],
    ["algorithms","Poseidon","","permute","110011","","","algorithms/src/poseidon/hash_many.rs:181"],
    ["algorithms","Poseidon","","squeeze","110011","","","algorithms/src/poseidon/hash_many.rs:91"],
    ["algorithms","Poseidon","","squeeze_internal","110011","","","algorithms/src/poseidon/hash_many.rs:101"],
    ["algorithms","Poseidon","HashMany","hash_many","110011","","","algorithms/src/poseidon/hash_many.rs:23"],
    ["algorithms","Poseidon","HashToGroup","hash_to_group","110011","","","algorithms/src/poseidon/hash_to_group.rs:25"],
    ["algorithms","Poseidon","HashToScalar","hash_to_scalar","110011","","","algorithms/src/poseidon/hash_to_scalar.rs:25"],
    ["algorithms","Poseidon","Inject","new","110011","","","algorithms/src/poseidon/mod.rs:74"],
    ["collections","<trait default>","PathHash","hash_empty","110011","","","collections/src/kary_merkle_tree/helpers/path_hash.rs:33"],
    ["collections","BHP","PathHash","hash_children","110011","","","collections/src/kary_merkle_tree/helpers/path_hash.rs:44"],
    ["collections","BooleanHash","Equal","is_equal","111111","Boolean::new on each input bit","Boolean::new on each input bit","collections/src/kary_merkle_tree/helpers/mod.rs:68"],
    ["collections","BooleanHash","Equal","is_not_equal","111111","Boolean::new on each input bit","Boolean::new on each input bit","collections/src/kary_merkle_tree/helpers/mod.rs:73"],
    ["collections","BooleanHash","Inject","new","111111","","","collections/src/kary_merkle_tree/helpers/mod.rs:38"],
    ["collections","BooleanHash","Ternary","ternary","111111","Boolean::new on the condition and each input bit","Boolean::new on the condition","collections/src/kary_merkle_tree/helpers/mod.rs:83"],
    ["collections","KaryMerklePath","","verify","111100","","","collections/src/kary_merkle_tree/verify.rs:21"],
    ["collections","KaryMerklePath","Inject","new","110111","","","collections/src/kary_merkle_tree/mod.rs:37"],
    ["collections","Keccak","PathHash","hash_children","110011","Boolean::new on each children bit (BooleanHash wires)","","collections/src/kary_merkle_tree/helpers/path_hash.rs:78"],
    ["collections","MerklePath","","verify","111111","U64::new on the leaf index (bit wires Boolean, equal to its low DEPTH bits); the leaf-hash and each level's hash_children circuits sound","the leaf-hash and each level's hash_children circuits complete","collections/src/merkle_tree/verify.rs:21"],
    ["collections","MerkleTree","","new","111101","","","collections/src/merkle_tree/mod.rs:110"],
    ["environment","(t0,ty,*)","Inject","new","110011","element type's Inject::new circuit satisfies seq-ij-elem-sound and seq-ij-elem-sound-not-error w.r.t. inject-impl (any verified element instance); variable mode","element type's Inject::new circuit satisfies seq-ij-elem-complete (witness seq-ij-elem-witness) w.r.t. inject-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element); variable mode; success direction only","environment/src/traits/inject.rs:77"],
    ["environment","(t0,ty,+)","ToBits","write_bits_be","110011","element type's write_bits_be circuit satisfies seq-be-elem-sound w.r.t. write-bits-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_be circuit satisfies seq-be-elem-complete (witness seq-be-elem-witness) w.r.t. write-bits-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:195"],
    ["environment","(t0,ty,+)","ToBits","write_bits_le","110011","element type's write_bits_le circuit satisfies seq-le-elem-sound w.r.t. write-bits-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_le circuit satisfies seq-le-elem-complete (witness seq-le-elem-witness) w.r.t. write-bits-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:188"],
    ["environment","(t0,ty,+)","ToBitsRaw","write_bits_raw_be","110011","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-sound w.r.t. write-bits-raw-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-complete (witness seq-raw-be-elem-witness) w.r.t. write-bits-raw-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:231"],
    ["environment","(t0,ty,+)","ToBitsRaw","write_bits_raw_le","110011","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-sound w.r.t. write-bits-raw-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-complete (witness seq-raw-le-elem-witness) w.r.t. write-bits-raw-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:224"],
    ["environment","<trait default>","Environment","assert","111111","","","environment/src/environment.rs:73"],
    ["environment","<trait default>","Environment","assert_eq","111111","","","environment/src/environment.rs:80"],
    ["environment","<trait default>","Environment","assert_neq","111111","","","environment/src/environment.rs:89"],
    ["environment","<trait default>","ToBits","to_bits_be","110011","element type's write_bits_be circuit satisfies seq-be-elem-sound w.r.t. write-bits-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_be circuit satisfies seq-be-elem-complete (witness seq-be-elem-witness) w.r.t. write-bits-be-impl","environment/src/traits/to_bits.rs:32"],
    ["environment","<trait default>","ToBits","to_bits_le","110011","element type's write_bits_le circuit satisfies seq-le-elem-sound w.r.t. write-bits-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_le circuit satisfies seq-le-elem-complete (witness seq-le-elem-witness) w.r.t. write-bits-le-impl","environment/src/traits/to_bits.rs:23"],
    ["environment","<trait default>","ToBitsRaw","to_bits_raw_be","110011","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-sound w.r.t. write-bits-raw-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-complete (witness seq-raw-be-elem-witness) w.r.t. write-bits-raw-be-impl","environment/src/traits/to_bits.rs:53"],
    ["environment","<trait default>","ToBitsRaw","to_bits_raw_le","110011","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-sound w.r.t. write-bits-raw-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-complete (witness seq-raw-le-elem-witness) w.r.t. write-bits-raw-le-impl","environment/src/traits/to_bits.rs:44"],
    ["environment","CanaryCircuit","Environment","enforce","111111","","","environment/src/canary_circuit.rs:128"],
    ["environment","Circuit","Environment","enforce","111111","","","environment/src/circuit.rs:152"],
    ["environment","TestnetCircuit","Environment","enforce","111111","","","environment/src/testnet_circuit.rs:128"],
    ["environment","Vec","Inject","new","110011","element type's Inject::new circuit satisfies seq-ij-elem-sound and seq-ij-elem-sound-not-error w.r.t. inject-impl (any verified element instance); variable mode","element type's Inject::new circuit satisfies seq-ij-elem-complete (witness seq-ij-elem-witness) w.r.t. inject-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element); variable mode; success direction only","environment/src/traits/inject.rs:61"],
    ["environment","Vec","ToBits","write_bits_be","110011","element type's write_bits_be circuit satisfies seq-be-elem-sound w.r.t. write-bits-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_be circuit satisfies seq-be-elem-complete (witness seq-be-elem-witness) w.r.t. write-bits-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:78"],
    ["environment","Vec","ToBits","write_bits_le","110011","element type's write_bits_le circuit satisfies seq-le-elem-sound w.r.t. write-bits-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_le circuit satisfies seq-le-elem-complete (witness seq-le-elem-witness) w.r.t. write-bits-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:71"],
    ["environment","Vec","ToBitsRaw","write_bits_raw_be","110011","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-sound w.r.t. write-bits-raw-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-complete (witness seq-raw-be-elem-witness) w.r.t. write-bits-raw-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:134"],
    ["environment","Vec","ToBitsRaw","write_bits_raw_le","110011","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-sound w.r.t. write-bits-raw-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-complete (witness seq-raw-le-elem-witness) w.r.t. write-bits-raw-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:127"],
    ["environment","[C]","ToBits","write_bits_be","110011","element type's write_bits_be circuit satisfies seq-be-elem-sound w.r.t. write-bits-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_be circuit satisfies seq-be-elem-complete (witness seq-be-elem-witness) w.r.t. write-bits-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:96"],
    ["environment","[C]","ToBits","write_bits_le","110011","element type's write_bits_le circuit satisfies seq-le-elem-sound w.r.t. write-bits-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_le circuit satisfies seq-le-elem-complete (witness seq-le-elem-witness) w.r.t. write-bits-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:89"],
    ["environment","[C]","ToBitsRaw","write_bits_raw_be","110011","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-sound w.r.t. write-bits-raw-be-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_be circuit satisfies seq-raw-be-elem-complete (witness seq-raw-be-elem-witness) w.r.t. write-bits-raw-be-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:150"],
    ["environment","[C]","ToBitsRaw","write_bits_raw_le","110011","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-sound w.r.t. write-bits-raw-le-impl (any verified element instance, e.g. seq-bool, seq-fld)","element type's write_bits_raw_le circuit satisfies seq-raw-le-elem-complete (witness seq-raw-le-elem-witness) w.r.t. write-bits-raw-le-impl; element wire blocks pairwise disjoint and disjoint from shared wires (fresh variables per element)","environment/src/traits/to_bits.rs:143"],
    ["network","AleoV0","Aleo","commit_bhp1024","110011","Boolean::new on each input bit","","network/src/v0.rs:183"],
    ["network","AleoV0","Aleo","commit_bhp256","110011","Boolean::new on each input bit","","network/src/v0.rs:168"],
    ["network","AleoV0","Aleo","commit_bhp512","110011","Boolean::new on each input bit","","network/src/v0.rs:173"],
    ["network","AleoV0","Aleo","commit_bhp768","110011","Boolean::new on each input bit","","network/src/v0.rs:178"],
    ["network","AleoV0","Aleo","commit_ped128","110011","Boolean::new on each input bit","","network/src/v0.rs:193"],
    ["network","AleoV0","Aleo","commit_ped64","110011","Boolean::new on each input bit","","network/src/v0.rs:188"],
    ["network","AleoV0","Aleo","commit_to_group_bhp1024","110011","Boolean::new on each input bit","","network/src/v0.rs:213"],
    ["network","AleoV0","Aleo","commit_to_group_bhp256","110011","Boolean::new on each input bit","","network/src/v0.rs:198"],
    ["network","AleoV0","Aleo","commit_to_group_bhp512","110011","Boolean::new on each input bit","","network/src/v0.rs:203"],
    ["network","AleoV0","Aleo","commit_to_group_bhp768","110011","Boolean::new on each input bit","","network/src/v0.rs:208"],
    ["network","AleoV0","Aleo","commit_to_group_ped128","110011","Boolean::new on each input bit","","network/src/v0.rs:223"],
    ["network","AleoV0","Aleo","commit_to_group_ped64","110011","Boolean::new on each input bit","","network/src/v0.rs:218"],
    ["network","AleoV0","Aleo","g_scalar_multiply","111111","","","network/src/v0.rs:158"],
    ["network","AleoV0","Aleo","hash_many_psd2","110011","","","network/src/v0.rs:303"],
    ["network","AleoV0","Aleo","hash_many_psd4","110011","","","network/src/v0.rs:308"],
    ["network","AleoV0","Aleo","hash_many_psd8","110011","","","network/src/v0.rs:313"],
    ["network","AleoV0","Aleo","hash_to_group_bhp1024","110011","Boolean::new on each input bit","","network/src/v0.rs:333"],
    ["network","AleoV0","Aleo","hash_to_group_bhp256","110011","Boolean::new on each input bit","","network/src/v0.rs:318"],
    ["network","AleoV0","Aleo","hash_to_group_bhp512","110011","Boolean::new on each input bit","","network/src/v0.rs:323"],
    ["network","AleoV0","Aleo","hash_to_group_bhp768","110011","Boolean::new on each input bit","","network/src/v0.rs:328"],
    ["network","AleoV0","Aleo","hash_to_group_ped128","110011","Boolean::new on each input bit","","network/src/v0.rs:343"],
    ["network","AleoV0","Aleo","hash_to_group_ped64","110011","Boolean::new on each input bit","","network/src/v0.rs:338"],
    ["network","AleoV0","Aleo","hash_to_group_psd2","110011","","","network/src/v0.rs:348"],
    ["network","AleoV0","Aleo","hash_to_group_psd4","110011","","","network/src/v0.rs:353"],
    ["network","AleoV0","Aleo","hash_to_group_psd8","110011","","","network/src/v0.rs:358"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd2","110011","","","network/src/v0.rs:363"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd4","110011","","","network/src/v0.rs:368"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd8","110011","","","network/src/v0.rs:373"],
    ["network","AleoV0","Aleo","verify_merkle_path_bhp","111111","U64::new on the leaf index (bit wires Boolean, equal to its low DEPTH bits); the leaf-hash and each level's hash_children circuits sound","the leaf-hash and each level's hash_children circuits complete","network/src/v0.rs:378"],
    ["network","AleoV0","Aleo","verify_merkle_path_psd","111111","U64::new on the leaf index (bit wires Boolean, equal to its low DEPTH bits); the leaf-hash and each level's hash_children circuits sound","the leaf-hash and each level's hash_children circuits complete","network/src/v0.rs:387"],
    ["network","AleoV0","Environment","enforce","111111","","","network/src/v0.rs:431"],
    ["program","","","compute_function_id","100000","","","program/src/function_id/mod.rs:21"],
    ["program","Argument","Equal","is_equal","110011","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-aeq-namesp)","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp); fresh wires carry snarkVM's witnesses (rec-feq-witnessp / rec-aeq-witnessp: ptx-eq-witnessp, the Field::is_not_equal bits / multipliers and AND chain of DynamicFuture::is_equal, ptx-bop-witnessp per fold step)","program/src/data/future/argument.rs:68"],
    ["program","Argument","Equal","is_not_equal","110011","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-aeq-namesp)","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp); fresh wires carry snarkVM's witnesses (rec-feq-witnessp / rec-aeq-witnessp: ptx-eq-witnessp, the Field::is_not_equal bits / multipliers and AND chain of DynamicFuture::is_equal, ptx-bop-witnessp per fold step)","program/src/data/future/argument.rs:78"],
    ["program","Argument","Inject","new","110011","the plaintext argument (or nested plaintext arguments) has distinct member names (ptx-distinct)","the argument wires carry their witness (rec-anew-witnessp)","program/src/data/future/argument.rs:33"],
    ["program","Argument","ToBits","write_bits_be","110011","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound)","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound); bit / range-check wires carry snarkVM's witnesses (rec-abits-witnessp)","program/src/data/future/argument.rs:119"],
    ["program","Argument","ToBits","write_bits_le","110011","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound)","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound); bit / range-check wires carry snarkVM's witnesses (rec-abits-witnessp)","program/src/data/future/argument.rs:93"],
    ["program","Boolean","Cast","cast","110011","Boolean::new on the input bit","Boolean::new on the input bit","program/src/data/literal/cast/boolean.rs:21"],
    ["program","Boolean","CastLossy","cast_lossy","110011","Boolean::new on the input bit","Boolean::new on the input bit","program/src/data/literal/cast_lossy/boolean.rs:25"],
    ["program","Ciphertext","","decrypt_symmetric","100000","","","program/src/data/ciphertext/decrypt.rs:20"],
    ["program","Ciphertext","","decrypt_with_randomizers","100000","","","program/src/data/ciphertext/decrypt.rs:30"],
    ["program","Ciphertext","Equal","is_equal","110011","","","program/src/data/ciphertext/equal.rs:22"],
    ["program","Ciphertext","Equal","is_not_equal","110011","","","program/src/data/ciphertext/equal.rs:36"],
    ["program","Ciphertext","Inject","new","110011","","","program/src/data/ciphertext/mod.rs:38"],
    ["program","Ciphertext","ToBits","write_bits_be","110011","","","program/src/data/ciphertext/to_bits.rs:29"],
    ["program","Ciphertext","ToBits","write_bits_le","110011","","","program/src/data/ciphertext/to_bits.rs:22"],
    ["program","DynamicFuture","Equal","is_equal","111111","","","program/src/data/dynamic/future/equal.rs:22"],
    ["program","DynamicFuture","Equal","is_not_equal","111111","","","program/src/data/dynamic/future/equal.rs:30"],
    ["program","DynamicFuture","Inject","new","110011","","","program/src/data/dynamic/future/mod.rs:53"],
    ["program","DynamicFuture","ToBits","write_bits_be","110011","","","program/src/data/dynamic/future/to_bits.rs:39"],
    ["program","DynamicFuture","ToBits","write_bits_le","110011","","","program/src/data/dynamic/future/to_bits.rs:23"],
    ["program","DynamicFuture","ToFields","to_fields","110011","","","program/src/data/dynamic/future/to_fields.rs:23"],
    ["program","DynamicRecord","","find","110011","Address::new on the owner","","program/src/data/dynamic/record/find.rs:20"],
    ["program","DynamicRecord","","from_record","100000","","","program/src/data/dynamic/record/mod.rs:146"],
    ["program","DynamicRecord","","merkleize_data","100000","","","program/src/data/dynamic/record/mod.rs:174"],
    ["program","DynamicRecord","Equal","is_equal","110011","Address::new on the owner, Group::new on the nonce, Integer::new on the version (points groupp, version bits boolean, 8 of them)","Address::new on the owner, Group::new on the nonce, Integer::new on the version (points groupp, version bits boolean, 8 of them)","program/src/data/dynamic/record/equal.rs:22"],
    ["program","DynamicRecord","Equal","is_not_equal","110011","Address::new on the owner, Group::new on the nonce, Integer::new on the version (points groupp, version bits boolean, 8 of them)","Address::new on the owner, Group::new on the nonce, Integer::new on the version (points groupp, version bits boolean, 8 of them)","program/src/data/dynamic/record/equal.rs:31"],
    ["program","DynamicRecord","Inject","new","110011","","","program/src/data/dynamic/record/mod.rs:81"],
    ["program","DynamicRecord","ToBits","write_bits_be","110011","Address::new on the owner, Group::new on the nonce, Integer::new on the version","","program/src/data/dynamic/record/to_bits.rs:37"],
    ["program","DynamicRecord","ToBits","write_bits_le","110011","Address::new on the owner, Group::new on the nonce, Integer::new on the version","","program/src/data/dynamic/record/to_bits.rs:22"],
    ["program","DynamicRecord","ToFields","to_fields","110011","Address::new on the owner, Group::new on the nonce, Integer::new on the version","","program/src/data/dynamic/record/to_fields.rs:22"],
    ["program","Entry","","find","110011","","","program/src/data/record/entry/find.rs:20"],
    ["program","Entry","","num_randomizers","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","","program/src/data/record/entry/num_randomizers.rs:20"],
    ["program","Entry","","to_fields_with_visibility_as_mode","100000","","","program/src/data/record/entry/to_fields.rs:20"],
    ["program","Entry","","write_bits_le_with_visibility_as_mode","100000","","","program/src/data/record/entry/to_bits.rs:27"],
    ["program","Entry","Equal","is_equal","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","1","program/src/data/record/entry/equal.rs:22"],
    ["program","Entry","Equal","is_not_equal","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","1","program/src/data/record/entry/equal.rs:32"],
    ["program","Entry","Inject","new","110000","Plaintext members as built by the caller: struct member names distinct (ptx-distinct; fixed by the program's struct definitions)","1","program/src/data/record/entry/mod.rs:41"],
    ["program","Entry","ToBits","write_bits_be","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","1","program/src/data/record/entry/to_bits.rs:60"],
    ["program","Entry","ToBits","write_bits_le","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","1","program/src/data/record/entry/to_bits.rs:55"],
    ["program","Entry","ToFields","to_fields","110000","Entry::new (Plaintext::new, Literal::new on each leaf; ptx-s-ventry-new-sound) on the input; constant wire ptx-one = 1","1","program/src/data/record/entry/to_fields.rs:42"],
    ["program","Field","Cast","cast","110011","","","program/src/data/literal/cast/field.rs:26"],
    ["program","Field","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/field.rs:25"],
    ["program","Future","Equal","is_equal","110011","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp)","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp); fresh wires carry snarkVM's witnesses (rec-feq-witnessp / rec-aeq-witnessp: ptx-eq-witnessp, the Field::is_not_equal bits / multipliers and AND chain of DynamicFuture::is_equal, ptx-bop-witnessp per fold step)","program/src/data/future/equal.rs:22"],
    ["program","Future","Equal","is_not_equal","110011","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp)","valuation over the base field, well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintexts typed by Plaintext::new, DynamicFuture field wires bound), symbol-listp names, and the DynamicFuture leaves' 11 wires bound (rec-feq-namesp / rec-aeq-namesp); fresh wires carry snarkVM's witnesses (rec-feq-witnessp / rec-aeq-witnessp: ptx-eq-witnessp, the Field::is_not_equal bits / multipliers and AND chain of DynamicFuture::is_equal, ptx-bop-witnessp per fold step)","program/src/data/future/equal.rs:39"],
    ["program","Future","Inject","new","110011","each plaintext argument has distinct member names (ptx-distinct; names are synthesis-time constants)","each argument wire carries its witness (rec-fnew-witnessp, via ptx-new-witnessp)","program/src/data/future/mod.rs:43"],
    ["program","Future","ToBits","write_bits_be","110011","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound)","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound); bit / range-check wires carry snarkVM's witnesses (rec-fbits-witnessp)","program/src/data/future/to_bits.rs:54"],
    ["program","Future","ToBits","write_bits_le","110011","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound)","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound); bit / range-check wires carry snarkVM's witnesses (rec-fbits-witnessp)","program/src/data/future/to_bits.rs:24"],
    ["program","Future","ToFields","to_fields","110011","rec-u-hyps (the constant-one wire u is 1), well-formed and typed wire trees (rec-fwp/rec-awp, rec-ftyped/rec-atyped: plaintext leaves typed by Plaintext::new, DynamicFuture field / bit / range-check wires bound)","as Future::write_bits_le (rec-future-write-bits-complete)","program/src/data/future/to_fields.rs:23"],
    ["program","HeaderLeaf","ToBits","write_bits_be","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/header_leaf.rs:72"],
    ["program","HeaderLeaf","ToBits","write_bits_le","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/header_leaf.rs:66"],
    ["program","Identifier","Equal","is_equal","111111","","","program/src/data/identifier/equal.rs:22"],
    ["program","Identifier","Equal","is_not_equal","111111","","","program/src/data/identifier/equal.rs:27"],
    ["program","Identifier","FromBits","from_bits_be","110010","Boolean::new on each input bit","","program/src/data/identifier/from_bits.rs:47"],
    ["program","Identifier","FromBits","from_bits_le","110010","Boolean::new on each input bit","","program/src/data/identifier/from_bits.rs:22"],
    ["program","Identifier","FromField","from_field","110010","","","program/src/data/identifier/from_field.rs:22"],
    ["program","Identifier","ToBits","write_bits_be","110011","","","program/src/data/identifier/to_bits.rs:27"],
    ["program","Identifier","ToBits","write_bits_le","110011","","","program/src/data/identifier/to_bits.rs:22"],
    ["program","IdentifierLiteral","Cast","cast","110011","IdentifierLiteral::new on the input bytes","IdentifierLiteral::new on the input bytes","program/src/data/literal/cast/identifier.rs:21"],
    ["program","InputID","Inject","new","100000","","","program/src/request/mod.rs:43"],
    ["program","Integer","Cast","cast","110011","Integer::new on the input bits","Integer::new on the input bits","program/src/data/literal/cast/integer.rs:27"],
    ["program","Integer","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/integer.rs:25"],
    ["program","Literal","","from_bits_be","100000","","","program/src/data/literal/from_bits.rs:46"],
    ["program","Literal","","from_bits_le","100000","","","program/src/data/literal/from_bits.rs:20"],
    ["program","Literal","Equal","is_equal","110011","Literal::new on each operand (the type facts of the matching arm: groupp points, scalarp, bit, int-valuep, string-typep, identifier-literalp, signature arm as in literal-signature-new-sound-unconditional); the internal-wire hypotheses of the per-type theorems are as in those rows","","program/src/data/literal/equal.rs:22"],
    ["program","Literal","Equal","is_not_equal","110011","Literal::new on each operand (the type facts of the matching arm: groupp points, scalarp, bit, int-valuep, string-typep, identifier-literalp, signature arm as in literal-signature-new-sound-unconditional); the internal-wire hypotheses of the per-type theorems are as in those rows","","program/src/data/literal/equal.rs:47"],
    ["program","Literal","Inject","new","111111","Scalar::to_bits_le on the scalar arm's wire","","program/src/data/literal/mod.rs:106"],
    ["program","Literal","ToBits","write_bits_be","110011","Literal::new on the input (type facts of the matching arm); public unit wire 1","","program/src/data/literal/to_bits.rs:27"],
    ["program","Literal","ToBits","write_bits_le","110011","Literal::new on the input (type facts of the matching arm); public unit wire 1","","program/src/data/literal/to_bits.rs:22"],
    ["program","Literal","ToFields","to_fields","110011","Literal::new on the input (the matching arm's sound theorem: bits, scalarp, groupp, string/identifier byte decoding)","","program/src/data/literal/to_fields.rs:22"],
    ["program","OutputID","","dynamic_future","111111","","","program/src/response/mod.rs:157"],
    ["program","OutputID","","dynamic_record","111111","","","program/src/response/mod.rs:147"],
    ["program","OutputID","","external_record","111111","","","program/src/response/mod.rs:127"],
    ["program","OutputID","","future","111111","","","program/src/response/mod.rs:137"],
    ["program","OutputID","","private","111111","","","program/src/response/mod.rs:94"],
    ["program","OutputID","","public","111111","","","program/src/response/mod.rs:84"],
    ["program","OutputID","","record","110101","","","program/src/response/mod.rs:104"],
    ["program","Owner","","decrypt","100000","","","program/src/data/record/helpers/owner.rs:145"],
    ["program","Owner","","encrypt","110001","Address::new on the owner address wires (the point is groupp)","","program/src/data/record/helpers/owner.rs:118"],
    ["program","Owner","","to_entry","110011","Address::new on the owner address","","program/src/data/record/helpers/owner.rs:86"],
    ["program","Owner","Equal","is_equal","110011","Address::new on each owner address","","program/src/data/record/helpers/owner.rs:98"],
    ["program","Owner","Equal","is_not_equal","110011","Address::new on each owner address","","program/src/data/record/helpers/owner.rs:107"],
    ["program","Owner","Inject","new","110011","","","program/src/data/record/helpers/owner.rs:33"],
    ["program","Plaintext","","encrypt","110000","the Literal leaf circuit meets the abstract ptx-leaf-bits-* contract and Plaintext::new (Literal::new on each leaf) ran on the input (as Plaintext::to_fields); Address::new on the address wires; Scalar::to_bits_be on the randomizer (the mul_assign bit wires are rev (scalar-bits-le s)), as for Group::mul","Group::mul witnesses (grp-mul-gadget-complete) and leaf witnesses, with those constraints mentioning only wires of the starting assignment (hpos-cs-boundp)","program/src/data/plaintext/encrypt.rs:20"],
    ["program","Plaintext","","encrypt_symmetric","110000","the Literal leaf circuit meets the abstract ptx-leaf-bits-* contract and Plaintext::new (Literal::new on each leaf) ran on the input (as Plaintext::to_fields); key wire bound in the field","leaf witnesses (ptx-bits-witnessp) and leaf constraints mention only wires of the starting assignment (hpos-cs-boundp)","program/src/data/plaintext/encrypt.rs:28"],
    ["program","Plaintext","","encrypt_with_randomizers","110000","the Literal leaf circuit meets the abstract ptx-leaf-bits-* contract and Plaintext::new (Literal::new on each leaf) ran on the input (as Plaintext::to_fields)","leaf witnesses (ptx-bits-witnessp) as for Plaintext::to_fields","program/src/data/plaintext/encrypt.rs:38"],
    ["program","Plaintext","","find","110011","","","program/src/data/plaintext/find.rs:20"],
    ["program","Plaintext","","from_bit_array","110001","","","program/src/data/plaintext/mod.rs:50"],
    ["program","Plaintext","","from_bits_be_internal","110000","","1","program/src/data/plaintext/from_bits.rs:123"],
    ["program","Plaintext","","from_bits_le_internal","110000","","1","program/src/data/plaintext/from_bits.rs:34"],
    ["program","Plaintext","","num_randomizers","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/num_randomizers.rs:20"],
    ["program","Plaintext","Equal","is_equal","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/equal.rs:22"],
    ["program","Plaintext","Equal","is_not_equal","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/equal.rs:52"],
    ["program","Plaintext","From","from","110000","","1","program/src/data/plaintext/from_fields.rs:20"],
    ["program","Plaintext","FromBits","from_bits_be","110000","","1","program/src/data/plaintext/from_bits.rs:27"],
    ["program","Plaintext","FromBits","from_bits_le","110000","","1","program/src/data/plaintext/from_bits.rs:22"],
    ["program","Plaintext","FromFields","from_fields","110000","","1","program/src/data/plaintext/from_fields.rs:36"],
    ["program","Plaintext","Inject","new","110000","Plaintext members as built by the caller: struct member names distinct (ptx-distinct; fixed by the program's struct definitions)","1","program/src/data/plaintext/mod.rs:77"],
    ["program","Plaintext","ToBits","write_bits_be","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_bits.rs:80"],
    ["program","Plaintext","ToBits","write_bits_le","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_bits.rs:24"],
    ["program","Plaintext","ToBitsRaw","write_bits_raw_be","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_bits_raw.rs:42"],
    ["program","Plaintext","ToBitsRaw","write_bits_raw_le","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_bits_raw.rs:20"],
    ["program","Plaintext","ToFields","to_fields","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_fields.rs:22"],
    ["program","Plaintext","ToFieldsRaw","to_fields_raw","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/to_fields_raw.rs:20"],
    ["program","Plaintext","Visibility","size_in_fields","110000","Plaintext::new (Literal::new on each leaf; ptx-s-vnew-sound) on the input; constant wire ptx-one = 1","1","program/src/data/plaintext/size_in_fields.rs:20"],
    ["program","ProgramID","","to_address","110011","Identifier::new on name and network (field values are the identifier fields)","","program/src/id/to_address.rs:20"],
    ["program","ProgramID","Equal","is_equal","111111","","","program/src/id/mod.rs:85"],
    ["program","ProgramID","Equal","is_not_equal","111111","","","program/src/id/mod.rs:90"],
    ["program","ProgramID","ToBits","write_bits_be","110011","","","program/src/id/to_bits.rs:27"],
    ["program","ProgramID","ToBits","write_bits_le","110011","","","program/src/id/to_bits.rs:22"],
    ["program","Record","","decrypt","100000","","","program/src/data/record/decrypt.rs:20"],
    ["program","Record","","decrypt_symmetric_unchecked","100000","","","program/src/data/record/decrypt.rs:34"],
    ["program","Record","","decrypt_with_randomizers","100000","","","program/src/data/record/decrypt.rs:44"],
    ["program","Record","","encrypt","110011","Record::new on the record wires (owner and nonce group points, entries typed); randomizer, to_bits_le and step wires bound","as Record::encrypt_symmetric","program/src/data/record/encrypt.rs:20"],
    ["program","Record","","encrypt_symmetric","110011","Record::new on the record wires (owner and nonce group points, entries typed); randomizer, to_bits_le and step wires bound","randomizer bits/range witnesses and canonical step witnesses of both scalar multiplications; nonce = randomizer * G; entry leaf witnesses; prefix and entry constraints mention only bound wires; Poseidon wire supply bound","program/src/data/record/encrypt.rs:27"],
    ["program","Record","","encrypt_symmetric_unchecked","110011","Record::new on the record wires (owner a group point, entries typed), view key a wire","entry leaf witnesses; entry constraints mention only bound wires; Poseidon wire supply bound","program/src/data/record/encrypt.rs:42"],
    ["program","Record","","encrypt_with_randomizers","110011","Record::new on the record wires (Address::new on the owner, Literal::new on each entry leaf)","the entry leaf witnesses (Literal::new) satisfy their constraints","program/src/data/record/encrypt.rs:52"],
    ["program","Record","","find","110011","none beyond well-formed wire trees (rec-record-datawp, access-listp path)","none (no constraints)","program/src/data/record/find.rs:20"],
    ["program","Record","","is_hiding","111111","Integer::new on the version","","program/src/data/record/mod.rs:155"],
    ["program","Record","","num_randomizers","110011","each entry plaintext typed and the entries' to_bits_le constraints hold (the size is computed from the bits, as in snarkVM)","entry plaintexts typed and the entries' bit wires carry snarkVM's witnesses (rec-record-data-bits-complete)","program/src/data/record/num_randomizers.rs:20"],
    ["program","Record","","serial_number","100000","","","program/src/data/record/serial_number.rs:20"],
    ["program","Record","","serial_number_from_gamma","100000","","","program/src/data/record/serial_number.rs:30"],
    ["program","Record","","to_commitment","100000","","","program/src/data/record/to_commitment.rs:20"],
    ["program","Record","Equal","is_equal","110011","owner / nonce injected with Group::new (14-wire lists, points groupp), version bits boolean (Integer::new), entry plaintexts typed (Plaintext::new); same entry count (otherwise the constant result is returned) (rec-record-eq-hyps)","as R1CS-SOUND-IF, plus snarkVM's witnesses: rec-deq-witnessp for the data fold, the Group::is_equal / Field::is_not_equal witnesses, and each non-folded AND / OR variable holding its value (ptx-bop-witnessp)","program/src/data/record/equal.rs:24"],
    ["program","Record","Equal","is_not_equal","110011","owner / nonce injected with Group::new (14-wire lists, points groupp), version bits boolean (Integer::new), entry plaintexts typed (Plaintext::new); same entry count (otherwise the constant result is returned) (rec-record-eq-hyps)","as R1CS-SOUND-IF, plus snarkVM's witnesses: rec-deq-witnessp for the data fold, the Group::is_equal / Field::is_not_equal witnesses, and each non-folded AND / OR variable holding its value (ptx-bop-witnessp)","program/src/data/record/equal.rs:45"],
    ["program","Record","Inject","new","110011","each entry plaintext has distinct member names (ptx-distinct; the names are synthesis-time constants)","each entry wire carries its plaintext's witness (ptx-new-witnessp) and plaintext-new does not fail on it; owner/nonce/version witnesses as in group-enforce-in-group-gadget-complete and int-new-gadget-complete","program/src/data/record/mod.rs:59"],
    ["program","Record","ToBits","write_bits_be","110011","owner / nonce points groupp (Address::new, Group::new), version bits boolean (Integer::new on the version), each entry plaintext typed (ptx-typed, i.e. Plaintext::new on each entry); owner/nonce bit wires and range-check wires bound (rec-record-bits-hyps)","owner / nonce points groupp (Address::new, Group::new), version bits boolean (Integer::new on the version), each entry plaintext typed (ptx-typed, i.e. Plaintext::new on each entry); owner/nonce bit wires and range-check wires bound (rec-record-bits-hyps); bit / range-check / is_hiding wires carry snarkVM's witnesses","program/src/data/record/to_bits.rs:63"],
    ["program","Record","ToBits","write_bits_le","110011","owner / nonce points groupp (Address::new, Group::new), version bits boolean (Integer::new on the version), each entry plaintext typed (ptx-typed, i.e. Plaintext::new on each entry); owner/nonce bit wires and range-check wires bound (rec-record-bits-hyps)","owner / nonce points groupp (Address::new, Group::new), version bits boolean (Integer::new on the version), each entry plaintext typed (ptx-typed, i.e. Plaintext::new on each entry); owner/nonce bit wires and range-check wires bound (rec-record-bits-hyps); bit / range-check / is_hiding wires carry snarkVM's witnesses","program/src/data/record/to_bits.rs:22"],
    ["program","Record","ToFields","to_fields","110011","owner / nonce points groupp (Address::new, Group::new), version bits boolean (Integer::new on the version), each entry plaintext typed (ptx-typed, i.e. Plaintext::new on each entry); owner/nonce bit wires and range-check wires bound (rec-record-bits-hyps)","as Record::write_bits_le (rec-record-write-bits-complete)","program/src/data/record/to_fields.rs:22"],
    ["program","Request","","check_input_ids","100000","","","program/src/request/verify.rs:124"],
    ["program","Request","","to_tpk","100000","","","program/src/request/to_tpk.rs:20"],
    ["program","Request","","verify","100000","","","program/src/request/verify.rs:25"],
    ["program","Request","Inject","new","100000","","","program/src/request/mod.rs:163"],
    ["program","Response","","from_outputs","100000","","","program/src/response/from_outputs.rs:20"],
    ["program","Response","","process_outputs_from_callback","100000","","","program/src/response/process_outputs_from_callback.rs:20"],
    ["program","Scalar","Cast","cast","110011","Scalar::new on the input scalar","Scalar::new on the input scalar","program/src/data/literal/cast/scalar.rs:27"],
    ["program","Scalar","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/scalar.rs:25"],
    ["program","StatePath","","verify","100000","","","program/src/state_path/verify.rs:55"],
    ["program","TransactionLeaf","ToBits","write_bits_be","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/transaction_leaf.rs:84"],
    ["program","TransactionLeaf","ToBits","write_bits_le","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/transaction_leaf.rs:77"],
    ["program","TransitionLeaf","ToBits","write_bits_be","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/transition_leaf.rs:101"],
    ["program","TransitionLeaf","ToBits","write_bits_le","110011","Integer::new on each integer field (boolean bit wires)","","program/src/state_path/helpers/transition_leaf.rs:93"],
    ["program","Value","","find","110011","rec-vfind-hyps: the owner point of a record / dynamic record is on the curve (Address::new); path a list of constant accesses","none (no constraints)","program/src/data/value/find.rs:20"],
    ["program","Value","Equal","is_equal","110011","same variant: rec-veq-hyps (operands' Inject facts: typed leaves, points on the curve, boolean version bits; fresh wires symbols bound); different variants: none","different variants: none; plaintext: ptx-eq-witnessp; future: rec-feq-witnessp; dynamic future: rec-dfeq-witnessp; record / dynamic record: rec-record-eq-complete / rec-dynamic-record-is-equal-complete via rec-value-eq-gadget-arms","program/src/data/value/equal.rs:22"],
    ["program","Value","Equal","is_not_equal","110011","same variant: rec-veq-hyps (operands' Inject facts: typed leaves, points on the curve, boolean version bits; fresh wires symbols bound); different variants: none","different variants: none; plaintext: ptx-eq-witnessp; future: rec-feq-witnessp; dynamic future: rec-dfeq-witnessp; record / dynamic record: rec-record-eq-complete / rec-dynamic-record-is-equal-complete via rec-value-eq-gadget-arms","program/src/data/value/equal.rs:38"],
    ["program","Value","Inject","new","110011","rec-vnew-hyps: plaintext member names distinct (ptx-distinct); record entry plaintexts distinct and entry names with distinct identifier fields (rec-vb-names-distinctp, the console IndexMap keys); input wires bound","plaintext: ptx-new-witnessp; future: rec-fnew-witnessp; dynamic future: none; record / dynamic record: the arm's component witnesses (rec-record-new-complete, rec-dynamic-record-new-complete)","program/src/data/value/mod.rs:45"],
    ["program","Value","ToBits","write_bits_be","110011","rec-vbits-hyps (what each arm's Inject establishes: typed leaves, points on the curve, boolean version bits; bit / range-check wires bound), u = 1","plaintext: ptx-bits-witnessp; future: rec-fbits-witnessp; dynamic future / dynamic record: rec-bits-witness-okp; record: rec-record-write-bits-complete via rec-value-write-bits-gadget-arms","program/src/data/value/to_bits.rs:35"],
    ["program","Value","ToBits","write_bits_le","110011","rec-vbits-hyps (what each arm's Inject establishes: typed leaves, points on the curve, boolean version bits; bit / range-check wires bound), u = 1","plaintext: ptx-bits-witnessp; future: rec-fbits-witnessp; dynamic future / dynamic record: rec-bits-witness-okp; record: rec-record-write-bits-complete via rec-value-write-bits-gadget-arms","program/src/data/value/to_bits.rs:23"],
    ["program","Value","ToBitsRaw","write_bits_raw_be","110011","as Value::write_bits (rec-vbits-hyps), u = 1","as Value::write_bits (rec-value-write-bits-complete)","program/src/data/value/to_bits_raw.rs:34"],
    ["program","Value","ToBitsRaw","write_bits_raw_le","110011","as Value::write_bits (rec-vbits-hyps), u = 1","as Value::write_bits (rec-value-write-bits-complete)","program/src/data/value/to_bits_raw.rs:21"],
    ["program","Value","ToFields","to_fields","110011","as Value::write_bits_le (rec-vbits-hyps), u = 1","as Value::write_bits_le (rec-value-write-bits-complete)","program/src/data/value/to_fields.rs:23"],
    ["program","Value","ToFieldsRaw","to_fields_raw","110011","as Value::write_bits_le (rec-vbits-hyps), u = 1","as Value::write_bits_le (rec-value-write-bits-complete)","program/src/data/value/to_fields_raw.rs:21"],
    ["types/address","Address","Compare","is_greater_than","110011","Address::new on each address input (public unit wire 1)","","types/address/src/compare.rs:27"],
    ["types/address","Address","Compare","is_greater_than_or_equal","110011","Address::new on each address input (public unit wire 1)","","types/address/src/compare.rs:37"],
    ["types/address","Address","Compare","is_less_than","110011","Address::new on each address input (public unit wire 1)","","types/address/src/compare.rs:22"],
    ["types/address","Address","Compare","is_less_than_or_equal","110011","Address::new on each address input (public unit wire 1)","","types/address/src/compare.rs:32"],
    ["types/address","Address","Equal","is_equal","111111","Address::new on each address input","","types/address/src/equal.rs:22"],
    ["types/address","Address","Equal","is_not_equal","111111","Address::new on each address input","","types/address/src/equal.rs:27"],
    ["types/address","Address","From","from","110011","","","types/address/src/helpers/from_field.rs:20"],
    ["types/address","Address","FromBits","from_bits_be","110011","Boolean::new on each input bit; fewer than p bits","","types/address/src/helpers/from_bits.rs:27"],
    ["types/address","Address","FromBits","from_bits_le","110011","Boolean::new on each input bit; fewer than p bits","","types/address/src/helpers/from_bits.rs:22"],
    ["types/address","Address","FromField","from_field","110011","","","types/address/src/helpers/from_field.rs:36"],
    ["types/address","Address","Inject","new","110011","","","types/address/src/lib.rs:57"],
    ["types/address","Address","Ternary","ternary","111111","Boolean::new on the condition and Address::new on each address input","","types/address/src/ternary.rs:23"],
    ["types/address","Address","ToBits","write_bits_be","111011","Address::new on the input","","types/address/src/helpers/to_bits.rs:27"],
    ["types/address","Address","ToBits","write_bits_le","111011","Address::new on the input","","types/address/src/helpers/to_bits.rs:22"],
    ["types/address","Field","From","from","111111","Address::new on the input","","types/address/src/helpers/to_field.rs:20"],
    ["types/boolean","Boolean","","assert_bits_are_zero","111111","Boolean::new on each input bit","","types/boolean/src/helpers/bits_are_zero.rs:21"],
    ["types/boolean","Boolean","","assert_less_than_or_equal_constant","111111","Boolean::new on each input bit","","types/boolean/src/helpers/comparator.rs:37"],
    ["types/boolean","Boolean","","is_less_than_or_equal_constant","111111","Boolean::new on each input bit","","types/boolean/src/helpers/comparator.rs:22"],
    ["types/boolean","Boolean","Adder","adder","111111","Boolean::new on each input bit","","types/boolean/src/helpers/adder.rs:23"],
    ["types/boolean","Boolean","BitAnd","bitand","111111","Boolean::new on each input bit","","types/boolean/src/and.rs:22"],
    ["types/boolean","Boolean","BitAndAssign","bitand_assign","111111","Boolean::new on each input bit","","types/boolean/src/and.rs:58"],
    ["types/boolean","Boolean","BitOr","bitor","111111","Boolean::new on each input bit","","types/boolean/src/or.rs:22"],
    ["types/boolean","Boolean","BitOrAssign","bitor_assign","111111","Boolean::new on each input bit","","types/boolean/src/or.rs:58"],
    ["types/boolean","Boolean","BitXor","bitxor","111111","Boolean::new on each input bit","","types/boolean/src/xor.rs:22"],
    ["types/boolean","Boolean","BitXorAssign","bitxor_assign","111111","Boolean::new on each input bit","","types/boolean/src/xor.rs:58"],
    ["types/boolean","Boolean","Equal","is_equal","111111","Boolean::new on each input bit","","types/boolean/src/equal.rs:22"],
    ["types/boolean","Boolean","Equal","is_not_equal","111111","Boolean::new on each input bit","","types/boolean/src/equal.rs:27"],
    ["types/boolean","Boolean","Inject","new","111111","","","types/boolean/src/lib.rs:62"],
    ["types/boolean","Boolean","Nand","nand","111111","Boolean::new on each input bit","","types/boolean/src/nand.rs:22"],
    ["types/boolean","Boolean","Nor","nor","111111","Boolean::new on each input bit","","types/boolean/src/nor.rs:22"],
    ["types/boolean","Boolean","Subtractor","subtractor","111111","Boolean::new on each input bit","","types/boolean/src/helpers/subtractor.rs:23"],
    ["types/boolean","Boolean","Ternary","ternary","111111","Boolean::new on the condition and on each operand","","types/boolean/src/ternary.rs:23"],
    ["types/field","Field","","even_square_root","111111","","","types/field/src/square_root.rs:50"],
    ["types/field","Field","","square_roots_flagged_nondeterministic","110010","the order of the two roots is not constrained (fsa-square-roots-flagged-unordered-sound); safe in the only production caller, Group::from_x_coordinate_flagged, which builds both candidate points and selects the one in the prime-order subgroup, so it does not depend on which root comes first","","types/field/src/square_root.rs:85"],
    ["types/field","Field","","to_non_unique_bits_le","110111","only called by Field::to_bits_le, which adds the bits_le <= p-1 range check that makes the bits unique (fb-field-bits.lisp proves the constraints force the bits to be boolean and sum to the input)","","types/field/src/helpers/to_bits.rs:68"],
    ["types/field","Field","Compare","is_greater_than","111111","","","types/field/src/compare.rs:79"],
    ["types/field","Field","Compare","is_greater_than_or_equal","111111","","","types/field/src/compare.rs:89"],
    ["types/field","Field","Compare","is_less_than","111111","","","types/field/src/compare.rs:22"],
    ["types/field","Field","Compare","is_less_than_or_equal","111111","","","types/field/src/compare.rs:84"],
    ["types/field","Field","Div","div","111111","","","types/field/src/div.rs:21"],
    ["types/field","Field","DivAssign","div_assign","111111","","","types/field/src/div.rs:53"],
    ["types/field","Field","DivUnchecked","div_unchecked","111111","only called by BHPHasher::hash_uncompressed, where a denominator cannot be zero while its numerator is; fb-field-div-unchecked.lisp proves soundness when the divisor is non-zero","","types/field/src/div_unchecked.rs:24"],
    ["types/field","Field","Equal","is_equal","111111","","","types/field/src/equal.rs:26"],
    ["types/field","Field","Equal","is_not_equal","111111","","","types/field/src/equal.rs:38"],
    ["types/field","Field","From","from","111111","","","types/field/src/lib.rs:151"],
    ["types/field","Field","FromBits","from_bits_be","111111","Boolean::new on each input bit","","types/field/src/helpers/from_bits.rs:72"],
    ["types/field","Field","FromBits","from_bits_le","111111","Boolean::new on each input bit","","types/field/src/helpers/from_bits.rs:24"],
    ["types/field","Field","FromBoolean","from_boolean","111111","Boolean::new on the input bit","","types/field/src/helpers/from_boolean.rs:22"],
    ["types/field","Field","Inv","inv","111111","","","types/field/src/inverse.rs:21"],
    ["types/field","Field","Inverse","inverse","111111","","","types/field/src/inverse.rs:37"],
    ["types/field","Field","Mul","mul","111111","","","types/field/src/mul.rs:21"],
    ["types/field","Field","MulAssign","mul_assign","111111","","","types/field/src/mul.rs:55"],
    ["types/field","Field","One","is_one","111111","","","types/field/src/helpers/one.rs:25"],
    ["types/field","Field","Pow","pow","111111","","","types/field/src/pow.rs:23"],
    ["types/field","Field","Square","square","111111","","","types/field/src/square.rs:21"],
    ["types/field","Field","SquareRoot","square_root","111111","","","types/field/src/square_root.rs:24"],
    ["types/field","Field","Ternary","ternary","111111","Boolean::new on the condition","","types/field/src/ternary.rs:23"],
    ["types/field","Field","ToBits","write_bits_be","111111","","","types/field/src/helpers/to_bits.rs:27"],
    ["types/field","Field","ToBits","write_bits_le","111111","","","types/field/src/helpers/to_bits.rs:22"],
    ["types/field","Field","ToLowerBits","to_lower_bits_be","111111","the caller passes k <= 252 (fb-field-to-lower-bits-be-gadget-sound). No production caller in circuit/ calls to_lower_bits_be directly. At k = 253 the circuit aliases.","","types/field/src/helpers/to_lower_bits.rs:56"],
    ["types/field","Field","ToLowerBits","to_lower_bits_le","111111","the caller passes k <= 252 (fb-field-to-lower-bits-le-gadget-sound). Every production caller in circuit/ does: Integer shl/shr (2*BITS <= 128), signed shl_checked (3*BITS <= 192), add/sub/compare (BITS+1), mul (BITS+BITS/2+1 <= 193), Integer from_field (BITS), Scalar add (252, 251), Scalar to_bits (251). At k = 253 the circuit aliases.","","types/field/src/helpers/to_lower_bits.rs:25"],
    ["types/field","Field","ToUpperBits","to_upper_bits_be","111101","","","types/field/src/helpers/to_upper_bits.rs:35"],
    ["types/field","Field","ToUpperBits","to_upper_bits_le","111101","","","types/field/src/helpers/to_upper_bits.rs:25"],
    ["types/field","Field","Zero","is_zero","111111","","","types/field/src/helpers/zero.rs:25"],
    ["types/group","Group","","enforce_double","110011","Group::new on self","","types/group/src/double.rs:67"],
    ["types/group","Group","","enforce_in_group","110011","","","types/group/src/lib.rs:101"],
    ["types/group","Group","","enforce_on_curve","111111","","","types/group/src/lib.rs:83"],
    ["types/group","Group","","from_x_coordinate","110011","","","types/group/src/helpers/from_x_coordinate.rs:21"],
    ["types/group","Group","","from_x_coordinate_flagged","110010","synthesis does not halt on x (the in-group witness division on (x, 0) is defined; where the funspec halts snarkVM halts and emits no constraint system); square-root order irrelevant (grp-from-x-flagged-gadget-sound)","","types/group/src/helpers/from_x_coordinate.rs:35"],
    ["types/group","Group","","from_xy_coordinates","110011","","","types/group/src/helpers/from_xy_coordinates.rs:21"],
    ["types/group","Group","","is_in_group","110011","Group::enforce_on_curve or Group::new on the input","","types/group/src/lib.rs:137"],
    ["types/group","Group","","mul_by_cofactor","110011","Group::new on the input","","types/group/src/helpers/mul_by_cofactor.rs:20"],
    ["types/group","Group","Add","add","110111","Group::new on each group input","","types/group/src/add.rs:21"],
    ["types/group","Group","AddAssign","add_assign","110011","Group::new on each group input","","types/group/src/add.rs:100"],
    ["types/group","Group","Double","double","110111","Group::new on the input","","types/group/src/double.rs:21"],
    ["types/group","Group","Equal","is_equal","111111","Group::new on each group input","","types/group/src/equal.rs:26"],
    ["types/group","Group","Equal","is_not_equal","111111","Group::new on each group input","","types/group/src/equal.rs:40"],
    ["types/group","Group","FromBits","from_bits_be","110011","Boolean::new on each input bit; fewer than p bits","","types/group/src/helpers/from_bits.rs:30"],
    ["types/group","Group","FromBits","from_bits_le","110011","Boolean::new on each input bit; fewer than p bits","","types/group/src/helpers/from_bits.rs:22"],
    ["types/group","Group","Inject","new","110011","","","types/group/src/lib.rs:65"],
    ["types/group","Group","Mul","mul","110011","Group::new on the group input and Scalar::to_bits_be on the scalar","","types/group/src/mul.rs:21"],
    ["types/group","Group","MulAssign","mul_assign","110011","Group::new on the group input and Scalar::to_bits_be on the scalar","","types/group/src/mul.rs:85"],
    ["types/group","Group","Sub","sub","110111","Group::new on each group input","","types/group/src/sub.rs:21"],
    ["types/group","Group","SubAssign","sub_assign","110011","Group::new on each group input","","types/group/src/sub.rs:43"],
    ["types/group","Group","Ternary","ternary","111111","Boolean::new on the condition and Group::new on each group input","","types/group/src/ternary.rs:23"],
    ["types/group","Group","ToBits","write_bits_be","111011","Group::new on the input","","types/group/src/helpers/to_bits.rs:27"],
    ["types/group","Group","ToBits","write_bits_le","111011","Group::new on the input","","types/group/src/helpers/to_bits.rs:22"],
    ["types/group","Group","Zero","is_zero","111111","Group::new on the input","","types/group/src/helpers/zero.rs:25"],
    ["types/integers","Integer","","from_field_lossy","110011","","","types/integers/src/helpers/from_field_lossy.rs:23"],
    ["types/integers","Integer","","karatsuba_multiply","110111","Integer::new on each integer input","","types/integers/src/mul_checked.rs:170"],
    ["types/integers","Integer","","mul_and_check","111111","Integer::new on each integer input","","types/integers/src/mul_checked.rs:129"],
    ["types/integers","Integer","","mul_with_flags","100010","weak guarantee only (int-mul-with-flags-gadget-sound, widths 8-64, and int-mul-with-flags-128-gadget-sound): the flag is a bit and flag = 0 implies the product is correct; safe in the only caller, pow_checked, which asserts the flag is unset exactly on the iterations whose product is selected, so a lying flag forces the witnessed product to equal the true product wherever it is used","","types/integers/src/pow_checked.rs:103"],
    ["types/integers","Integer","","to_scalar","111111","Integer::new on the input","","types/integers/src/helpers/to_scalar.rs:20"],
    ["types/integers","Integer","","unsigned_division_via_witness","111111","Integer::new on each integer input","","types/integers/src/div_wrapped.rs:58"],
    ["types/integers","Integer","AbsChecked","abs_checked","111111","Integer::new on the input","","types/integers/src/abs_checked.rs:21"],
    ["types/integers","Integer","AbsWrapped","abs_wrapped","111111","Integer::new on the input","","types/integers/src/abs_wrapped.rs:21"],
    ["types/integers","Integer","Add","add","111111","Integer::new on each integer input","","types/integers/src/add_checked.rs:21"],
    ["types/integers","Integer","AddAssign","add_assign","111111","Integer::new on each integer input","","types/integers/src/add_checked.rs:53"],
    ["types/integers","Integer","AddChecked","add_checked","111111","Integer::new on each integer input","","types/integers/src/add_checked.rs:69"],
    ["types/integers","Integer","AddWrapped","add_wrapped","111111","Integer::new on each integer input","","types/integers/src/add_wrapped.rs:22"],
    ["types/integers","Integer","BitAnd","bitand","111111","Integer::new on each integer input","","types/integers/src/and.rs:22"],
    ["types/integers","Integer","BitAndAssign","bitand_assign","111111","Integer::new on each integer input","","types/integers/src/and.rs:58"],
    ["types/integers","Integer","BitOr","bitor","111111","Integer::new on each integer input","","types/integers/src/or.rs:22"],
    ["types/integers","Integer","BitOrAssign","bitor_assign","111111","Integer::new on each integer input","","types/integers/src/or.rs:58"],
    ["types/integers","Integer","BitXor","bitxor","111111","Integer::new on each integer input","","types/integers/src/xor.rs:22"],
    ["types/integers","Integer","BitXorAssign","bitxor_assign","111111","Integer::new on each integer input","","types/integers/src/xor.rs:58"],
    ["types/integers","Integer","Compare","is_greater_than","111111","Integer::new on each integer input","","types/integers/src/compare.rs:56"],
    ["types/integers","Integer","Compare","is_greater_than_or_equal","111111","Integer::new on each integer input","","types/integers/src/compare.rs:66"],
    ["types/integers","Integer","Compare","is_less_than","111111","Integer::new on each integer input","","types/integers/src/compare.rs:22"],
    ["types/integers","Integer","Compare","is_less_than_or_equal","111111","Integer::new on each integer input","","types/integers/src/compare.rs:61"],
    ["types/integers","Integer","Div","div","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/div_checked.rs:21"],
    ["types/integers","Integer","DivAssign","div_assign","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/div_checked.rs:53"],
    ["types/integers","Integer","DivChecked","div_checked","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/div_checked.rs:69"],
    ["types/integers","Integer","DivWrapped","div_wrapped","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/div_wrapped.rs:22"],
    ["types/integers","Integer","Equal","is_equal","111111","Integer::new on each integer input","","types/integers/src/equal.rs:24"],
    ["types/integers","Integer","Equal","is_not_equal","111111","Integer::new on each integer input","","types/integers/src/equal.rs:48"],
    ["types/integers","Integer","FromBits","from_bits_be","111111","Boolean::new on each input bit","","types/integers/src/helpers/from_bits.rs:38"],
    ["types/integers","Integer","FromBits","from_bits_le","111111","Boolean::new on each input bit","","types/integers/src/helpers/from_bits.rs:22"],
    ["types/integers","Integer","FromField","from_field","111111","","","types/integers/src/helpers/from_field.rs:26"],
    ["types/integers","Integer","Inject","new","111111","","","types/integers/src/lib.rs:109"],
    ["types/integers","Integer","Modulo","modulo","111111","Integer::new on each integer input; variable operands","divisor not zero; snarkVM witnesses; variable operands","types/integers/src/modulo.rs:22"],
    ["types/integers","Integer","Mul","mul","110111","Integer::new on each integer input","","types/integers/src/mul_checked.rs:21"],
    ["types/integers","Integer","MulAssign","mul_assign","110111","Integer::new on each integer input","","types/integers/src/mul_checked.rs:53"],
    ["types/integers","Integer","MulChecked","mul_checked","110111","Integer::new on each integer input","","types/integers/src/mul_checked.rs:85"],
    ["types/integers","Integer","MulWrapped","mul_wrapped","110011","Integer::new on each integer input","","types/integers/src/mul_wrapped.rs:22"],
    ["types/integers","Integer","Neg","neg","111111","Integer::new on a signed input","","types/integers/src/neg.rs:22"],
    ["types/integers","Integer","One","is_one","111111","Integer::new on the input","","types/integers/src/helpers/one.rs:25"],
    ["types/integers","Integer","Pow","pow","110111","Integer::new on each integer input; variable base and exponent","result in range (spec not error); variable base and exponent","types/integers/src/pow_checked.rs:23"],
    ["types/integers","Integer","PowChecked","pow_checked","110111","Integer::new on each integer input; variable base and exponent","result in range (spec not error); variable base and exponent","types/integers/src/pow_checked.rs:43"],
    ["types/integers","Integer","PowWrapped","pow_wrapped","110011","Integer::new on the base and on the exponent; variable base and exponent","variable base and exponent","types/integers/src/pow_wrapped.rs:22"],
    ["types/integers","Integer","Rem","rem","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/rem_checked.rs:21"],
    ["types/integers","Integer","RemAssign","rem_assign","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/rem_checked.rs:53"],
    ["types/integers","Integer","RemChecked","rem_checked","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/rem_checked.rs:69"],
    ["types/integers","Integer","RemWrapped","rem_wrapped","111111","Integer::new on each integer input; variable operands","divisor not zero (and not MIN / -1 for checked forms); variable operands","types/integers/src/rem_wrapped.rs:22"],
    ["types/integers","Integer","Shl","shl","111111","Integer::new on each integer input; variable operands","e < n and x*2^e in range (spec not error); variable operands","types/integers/src/shl_checked.rs:21"],
    ["types/integers","Integer","ShlAssign","shl_assign","110111","Integer::new on each integer input; variable operands","e < n and x*2^e in range (spec not error); variable operands","types/integers/src/shl_checked.rs:53"],
    ["types/integers","Integer","ShlChecked","shl_checked","110111","Integer::new on each integer input; variable operands","e < n and x*2^e in range (spec not error); variable operands","types/integers/src/shl_checked.rs:69"],
    ["types/integers","Integer","ShlWrapped","shl_wrapped","100111","variable operands","variable operands","types/integers/src/shl_wrapped.rs:22"],
    ["types/integers","Integer","Shr","shr","110011","variable operands","variable operands","types/integers/src/shr_checked.rs:21"],
    ["types/integers","Integer","ShrAssign","shr_assign","110111","variable operands","variable operands","types/integers/src/shr_checked.rs:53"],
    ["types/integers","Integer","ShrChecked","shr_checked","110111","variable operands","variable operands","types/integers/src/shr_checked.rs:69"],
    ["types/integers","Integer","ShrWrapped","shr_wrapped","100111","variable operands","variable operands","types/integers/src/shr_wrapped.rs:22"],
    ["types/integers","Integer","Sub","sub","111111","Integer::new on each integer input","","types/integers/src/sub_checked.rs:21"],
    ["types/integers","Integer","SubAssign","sub_assign","111111","Integer::new on each integer input","","types/integers/src/sub_checked.rs:53"],
    ["types/integers","Integer","SubChecked","sub_checked","111111","Integer::new on each integer input","","types/integers/src/sub_checked.rs:69"],
    ["types/integers","Integer","SubWrapped","sub_wrapped","110011","Integer::new on each integer input","","types/integers/src/sub_wrapped.rs:22"],
    ["types/integers","Integer","Ternary","ternary","111111","Boolean::new on the condition and Integer::new on each integer input","","types/integers/src/ternary.rs:23"],
    ["types/integers","Integer","ToField","to_field","111111","Integer::new on the input","","types/integers/src/helpers/to_field.rs:22"],
    ["types/integers","Integer","ToFields","to_fields","111111","Integer::new on the input","","types/integers/src/helpers/to_fields.rs:22"],
    ["types/integers","Integer","Zero","is_zero","111111","Integer::new on the input","","types/integers/src/helpers/zero.rs:25"],
    ["types/scalar","Scalar","","from_field_lossy","110011","","","types/scalar/src/helpers/from_field_lossy.rs:23"],
    ["types/scalar","Scalar","Add","add","110011","Scalar::to_bits_le on each operand (scalarp)","","types/scalar/src/add.rs:21"],
    ["types/scalar","Scalar","AddAssign","add_assign","110011","Scalar::to_bits_le on each operand (scalarp)","","types/scalar/src/add.rs:53"],
    ["types/scalar","Scalar","Compare","is_greater_than","111011","Scalar::to_bits_le on each operand","","types/scalar/src/compare.rs:45"],
    ["types/scalar","Scalar","Compare","is_greater_than_or_equal","111011","Scalar::to_bits_le on each operand","","types/scalar/src/compare.rs:55"],
    ["types/scalar","Scalar","Compare","is_less_than","111011","Scalar::to_bits_le on each operand","","types/scalar/src/compare.rs:22"],
    ["types/scalar","Scalar","Compare","is_less_than_or_equal","111011","Scalar::to_bits_le on each operand","","types/scalar/src/compare.rs:50"],
    ["types/scalar","Scalar","Equal","is_equal","111111","Scalar::to_bits_le on each operand","","types/scalar/src/equal.rs:24"],
    ["types/scalar","Scalar","Equal","is_not_equal","111111","Scalar::to_bits_le on each operand","","types/scalar/src/equal.rs:31"],
    ["types/scalar","Scalar","FromBits","from_bits_be","110011","Boolean::new on each input bit","","types/scalar/src/helpers/from_bits.rs:86"],
    ["types/scalar","Scalar","FromBits","from_bits_le","110011","Boolean::new on each input bit","","types/scalar/src/helpers/from_bits.rs:24"],
    ["types/scalar","Scalar","FromField","from_field","111011","","","types/scalar/src/helpers/from_field.rs:28"],
    ["types/scalar","Scalar","One","is_one","111111","Scalar::to_bits_le on the operand","","types/scalar/src/helpers/one.rs:25"],
    ["types/scalar","Scalar","Ternary","ternary","111111","Boolean::new on the condition and Scalar::to_bits_le on each scalar operand","","types/scalar/src/ternary.rs:23"],
    ["types/scalar","Scalar","ToBits","write_bits_be","110011","","","types/scalar/src/helpers/to_bits.rs:27"],
    ["types/scalar","Scalar","ToBits","write_bits_le","110011","","","types/scalar/src/helpers/to_bits.rs:22"],
    ["types/scalar","Scalar","Zero","is_zero","111111","Scalar::to_bits_le on the operand","","types/scalar/src/helpers/zero.rs:25"],
    ["types/string","","","is_invalid_digit_offset","111111","Boolean::new on each input bit","","types/string/src/identifier_literal/mod.rs:240"],
    ["types/string","","","is_invalid_lowercase_offset","111111","Boolean::new on each input bit and ByteValidationData::new on the data","","types/string/src/identifier_literal/mod.rs:296"],
    ["types/string","","","is_invalid_uppercase_offset","111111","Boolean::new on each input bit and ByteValidationData::new on the data","","types/string/src/identifier_literal/mod.rs:268"],
    ["types/string","","","validate_byte","111111","Boolean::new on each input bit","","types/string/src/identifier_literal/mod.rs:310"],
    ["types/string","","","validate_identifier_bytes","111111","U8::new on each byte (the bit boolean checks)","","types/string/src/identifier_literal/mod.rs:147"],
    ["types/string","","","validate_trailing_nulls","111111","validate_byte on each null flag","","types/string/src/identifier_literal/mod.rs:381"],
    ["types/string","ByteValidationData","","new","111111","Boolean::new on each input bit","","types/string/src/identifier_literal/mod.rs:206"],
    ["types/string","IdentifierLiteral","Equal","is_equal","111111","Literal::new identifier arm on each operand (literal-identifier-new-sound)","","types/string/src/identifier_literal/equal.rs:22"],
    ["types/string","IdentifierLiteral","Equal","is_not_equal","111111","Literal::new identifier arm on each operand (literal-identifier-new-sound)","","types/string/src/identifier_literal/equal.rs:27"],
    ["types/string","IdentifierLiteral","FromBits","from_bits_be","110111","Boolean::new on each input bit","","types/string/src/identifier_literal/helpers/from_bits.rs:50"],
    ["types/string","IdentifierLiteral","FromBits","from_bits_le","110111","Boolean::new on each input bit","","types/string/src/identifier_literal/helpers/from_bits.rs:26"],
    ["types/string","IdentifierLiteral","FromField","from_field","110111","(public unit wire 1)","","types/string/src/identifier_literal/helpers/from_field.rs:22"],
    ["types/string","IdentifierLiteral","ToBits","write_bits_be","111111","Literal::new identifier arm on the input (literal-identifier-new-sound; id-decode-rows-matchp)","","types/string/src/identifier_literal/helpers/to_bits.rs:29"],
    ["types/string","IdentifierLiteral","ToBits","write_bits_le","111111","Literal::new identifier arm on the input (literal-identifier-new-sound; id-decode-rows-matchp)","","types/string/src/identifier_literal/helpers/to_bits.rs:22"],
    ["types/string","IdentifierLiteral","ToField","to_field","111111","Literal::new identifier arm on the input (literal-identifier-new-sound; id-decode-rows-matchp)","","types/string/src/identifier_literal/helpers/to_field.rs:22"],
    ["types/string","IdentifierLiteral","ToFields","to_fields","111111","Literal::new identifier arm on the input (literal-identifier-new-sound; id-decode-rows-matchp)","","types/string/src/identifier_literal/helpers/to_fields.rs:22"],
  ],
  e: [
    [0,98],
    [1,98],
    [2,343],[2,425],
    [3,2],
    [4,112],
    [7,347],
    [8,352],[8,431],
    [9,353],
    [10,354],
    [12,0],
    [13,24],
    [14,1],[14,98],[14,425],
    [16,15],
    [17,5],
    [18,6],
    [19,7],
    [20,8],[20,431],
    [21,9],[21,432],
    [22,10],[22,433],
    [25,98],
    [26,27],
    [27,28],
    [28,29],
    [29,309],[29,342],
    [31,317],[31,334],
    [32,398],
    [33,398],
    [34,36],
    [35,71],
    [37,38],
    [38,39],
    [44,41],[44,42],
    [45,46],
    [48,31],[48,47],
    [49,418],
    [54,53],
    [55,295],
    [56,299],
    [60,324],
    [69,317],
    [77,7],[77,19],[77,30],[77,50],[77,55],[77,58],[77,61],[77,62],[77,120],[77,129],[77,134],[77,143],[77,153],[77,161],[77,175],[77,182],[77,198],[77,213],[77,241],[77,248],[77,261],[77,278],[77,295],[77,347],[77,387],[77,441],
    [99,47],
    [100,47],
    [101,47],
    [108,48],
    [109,48],
    [110,48],
    [111,49],
    [112,49],
    [113,49],
    [117,71],
    [123,124],
    [124,279],[124,315],[124,352],[124,414],[124,431],
    [125,101],
    [132,310],
    [133,132],
    [135,325],
    [136,326],
    [137,71],
    [138,209],
    [139,140],
    [141,272],[141,310],[141,343],
    [142,141],
    [144,280],[144,325],[144,353],
    [145,281],[145,326],[145,354],
    [146,71],
    [148,220],[148,289],
    [149,150],
    [150,295],
    [153,129],[153,213],
    [155,150],
    [156,149],
    [157,277],[157,320],[157,331],[157,335],[157,386],[157,429],[157,446],
    [158,31],[158,71],[158,324],[158,336],[158,356],[158,418],
    [159,167],[159,222],
    [160,168],[160,223],
    [162,70],
    [164,71],
    [165,325],
    [166,326],
    [167,310],
    [168,311],
    [169,170],
    [170,314],
    [171,71],
    [172,173],
    [173,326],
    [174,449],
    [175,347],
    [176,71],[176,283],[176,394],[176,415],[176,417],
    [177,71],[177,360],[177,385],[177,415],
    [178,17],[178,313],[178,345],[178,427],[178,444],
    [179,18],[179,314],[179,346],[179,428],[179,445],
    [182,295],
    [195,209],
    [198,129],[198,278],
    [199,200],
    [200,101],
    [202,289],
    [203,209],
    [206,220],
    [209,212],
    [210,204],
    [211,205],
    [212,71],
    [214,70],
    [215,71],
    [216,70],
    [217,71],[217,73],
    [218,71],
    [219,73],
    [220,71],
    [221,109],
    [222,167],
    [223,168],
    [226,227],
    [227,101],
    [228,193],
    [229,230],
    [230,98],
    [231,101],
    [232,194],[232,201],
    [236,108],
    [237,71],[237,88],[237,339],
    [239,196],[239,343],
    [240,197],[240,344],
    [242,70],[242,234],[242,353],
    [243,71],[243,234],[243,354],
    [244,71],
    [245,108],[245,238],
    [246,98],
    [247,272],
    [248,261],
    [249,186],[249,187],[249,188],[249,189],[249,190],[249,191],[249,192],[249,238],
    [250,186],[250,187],[250,188],[250,189],[250,190],[250,191],[250,238],[250,261],
    [251,71],[251,430],[251,434],
    [252,71],
    [253,114],[253,299],[253,326],
    [254,325],
    [255,326],
    [256,325],
    [257,326],
    [261,134],[261,143],[261,213],[261,241],
    [267,219],
    [268,270],
    [269,270],
    [271,269],
    [272,343],
    [273,344],
    [274,277],
    [275,345],
    [276,346],
    [277,335],
    [278,347],
    [279,352],
    [280,353],
    [281,354],
    [284,285],
    [286,287],[286,289],[286,291],
    [287,288],
    [289,290],
    [291,292],
    [293,294],
    [294,291],
    [296,287],
    [297,287],
    [298,287],[298,289],[298,291],
    [299,287],[299,289],
    [300,70],
    [301,323],[301,324],[301,393],
    [302,318],[302,342],
    [303,305],
    [304,305],
    [305,299],
    [306,304],
    [307,308],
    [308,317],[308,318],[308,319],
    [309,289],[309,317],
    [310,311],
    [311,295],
    [312,282],
    [313,314],
    [314,283],[314,284],[314,318],[314,342],
    [315,282],[315,312],
    [316,317],
    [318,319],
    [319,289],
    [320,310],
    [321,318],[321,319],[321,324],
    [322,318],
    [324,318],
    [325,326],
    [326,284],[326,302],
    [327,328],
    [328,318],[328,342],
    [329,318],[329,342],
    [330,329],
    [331,310],
    [332,340],[332,342],[332,350],
    [333,332],[333,334],[333,342],
    [334,350],
    [335,337],
    [336,301],[336,324],[336,338],[336,350],
    [337,333],
    [339,342],
    [341,340],
    [342,340],[342,350],
    [343,287],[343,310],
    [344,343],
    [345,313],
    [346,314],
    [347,333],
    [348,349],
    [349,70],[349,340],[349,342],[349,352],
    [350,340],
    [351,340],[351,350],
    [352,324],
    [353,325],
    [354,326],
    [355,287],[355,310],
    [356,71],
    [357,328],
    [358,283],
    [359,357],
    [360,428],
    [361,366],[361,391],
    [362,412],
    [363,413],[363,414],
    [364,365],
    [365,366],
    [366,287],[366,328],[366,368],
    [367,328],
    [368,287],[368,288],[368,369],
    [369,287],[369,288],
    [370,289],[370,290],[370,371],
    [371,289],[371,290],
    [372,291],[372,292],[372,373],
    [373,291],[373,292],
    [374,376],
    [375,376],
    [376,287],[376,328],[376,368],
    [377,375],
    [378,379],
    [379,380],
    [380,287],[380,363],[380,368],[380,381],[380,382],[380,393],[380,413],[380,414],
    [381,361],
    [382,287],[382,368],
    [383,382],
    [384,385],
    [385,283],
    [386,328],
    [387,287],[387,295],[387,368],
    [388,401],
    [389,390],
    [390,391],
    [391,287],[391,289],[391,358],[391,368],[391,370],
    [392,328],
    [393,366],
    [394,382],
    [395,396],
    [396,287],[396,289],[396,363],[396,368],[396,370],[396,387],[396,391],[396,414],
    [397,392],[397,414],
    [398,399],
    [399,400],
    [400,287],[400,363],[400,368],[400,382],[400,393],[400,401],[400,413],[400,414],
    [401,361],
    [402,403],
    [403,404],
    [404,283],[404,324],[404,328],[404,391],[404,396],
    [405,324],[405,328],[405,392],
    [406,407],
    [407,408],
    [408,283],[408,387],
    [409,324],[409,328],[409,361],[409,363],[409,367],[409,381],[409,413],[409,414],
    [410,411],
    [411,412],
    [412,287],[412,328],[412,368],
    [413,328],
    [414,299],
    [415,314],
    [416,415],
    [417,382],
    [418,71],[418,428],
    [419,420],
    [420,328],
    [421,423],
    [422,423],
    [423,295],[423,342],
    [424,422],
    [425,310],
    [426,425],
    [427,428],
    [428,283],[428,284],[428,342],[428,419],[428,420],
    [429,71],[429,428],
    [430,425],
    [431,324],
    [432,433],
    [433,284],[433,328],
    [434,425],
    [435,287],[435,289],
    [436,287],[436,289],
    [437,287],[437,291],
    [438,287],[438,441],
    [441,287],
    [444,445],
    [445,283],
    [446,71],[446,445],
    [447,448],
    [449,314],
    [450,449],
  ],
  d: [
    ["Inject::new",[7,19,30,50,55,58,62,77,120,129,134,143,153,161,175,182,198,213,241,248,261,278,295,347,387]],
    ["Ternary::ternary",[8,20,56,279,299,324,352,414,431]],
    ["add",[340,364,419]],
    ["bitand",[287,368]],
    ["bitor",[289,370]],
    ["bitxor",[291,372]],
    ["cast",[123,157,174,176,251]],
    ["cast_lossy",[124,158,177,252]],
    ["commit",[26,37]],
    ["commit_uncompressed",[27,38]],
    ["encrypt_symmetric",[200,230]],
    ["find",[138,147,202,233,258]],
    ["hash_children",[52,59]],
    ["hash_uncompressed",[28,29,39]],
    ["is_equal",[2,15,53,118,127,132,141,151,159,167,180,196,207,222,239,259,272,293,310,343,382,425,442]],
    ["is_less_than",[270,305,376,423]],
    ["is_less_than_or_equal",[271,306,377,424]],
    ["is_not_equal",[3,16,54,119,128,133,142,152,160,168,181,197,208,223,240,260,273,294,311,344,383,426,443]],
    ["is_one",[320,394,430]],
    ["is_zero",[331,355,417,434]],
    ["mul",[318,348,389]],
    ["num_randomizers",[148,206]],
    ["op &=",[287,288]],
    ["op *",[318,348,389]],
    ["op +",[340,364,419]],
    ["op +=",[340,341,364,365,419,420]],
    ["op -",[350,410]],
    ["op |=",[289,290]],
    ["pow",[321,395]],
    ["t0::new",[7,19,30,50,55,58,61,77,120,129,134,143,153,161,175,182,198,213,241,248,261,278,295,347,387,441]],
    ["to_address",[1,25,221]],
    ["to_field",[415,449]],
    ["to_fields",[11,23,137,146,156,164,185,218,244,266,416,450]],
    ["ty::new",[7,19,30,50,55,58,61,77,120,129,134,143,153,161,175,182,198,213,241,248,261,278,295,347,387,441]],
    ["verify",[14,57,60,247,253]],
    ["write_bits_be",[9,21,63,78,82,121,130,135,144,154,162,165,172,183,214,224,242,254,256,262,280,325,353,432,447]],
    ["write_bits_le",[10,22,64,79,83,122,131,136,145,155,163,166,173,184,215,225,243,255,257,263,281,326,354,433,448]],
    ["write_bits_raw_be",[65,80,84,216,264]],
    ["write_bits_raw_le",[66,81,85,217,265]],
  ],
  de: [
    [1,24],
    [5,24],
    [6,24],
    [11,31],
    [14,14],[14,24],
    [15,14],
    [17,24],
    [18,24],
    [23,31],[23,32],
    [24,24],
    [27,24],
    [29,24],
    [30,24],[30,25],
    [31,24],
    [34,36],
    [36,24],
    [38,24],
    [39,24],
    [40,24],[40,25],
    [41,25],
    [42,25],
    [43,28],
    [44,24],
    [46,24],
    [47,24],
    [48,24],
    [50,24],
    [51,12],
    [52,36],
    [53,14],
    [57,14],[57,15],[57,28],
    [58,0],
    [59,36],
    [61,24],
    [62,29],[62,33],
    [63,35],
    [64,36],
    [65,37],
    [66,38],
    [70,35],
    [71,36],
    [72,37],
    [73,38],
    [78,35],
    [79,36],
    [80,37],
    [81,38],
    [82,35],
    [83,36],
    [84,37],
    [85,38],
    [86,8],
    [87,8],
    [88,8],
    [89,8],
    [90,8],
    [91,8],
    [92,9],
    [93,9],
    [94,9],
    [95,9],
    [96,9],
    [97,9],
    [98,24],
    [102,13],
    [103,13],
    [104,13],
    [105,13],
    [106,13],
    [107,13],
    [114,34],
    [115,34],
    [118,14],
    [119,17],
    [120,0],
    [121,35],
    [122,36],
    [123,6],
    [126,26],
    [127,22],
    [128,17],[128,27],
    [129,0],
    [130,23],[130,26],[130,35],
    [131,23],[131,26],[131,36],
    [134,0],
    [140,31],[140,32],
    [141,14],
    [143,0],
    [144,35],
    [145,36],
    [147,11],
    [151,14],
    [152,17],
    [154,35],
    [155,36],
    [157,4],
    [159,14],[159,22],
    [160,17],[160,27],
    [161,0],
    [162,35],
    [163,36],
    [165,35],
    [166,36],
    [174,6],
    [176,4],[176,6],
    [177,7],
    [180,14],
    [181,17],
    [183,35],
    [184,36],
    [185,31],[185,32],
    [192,14],
    [193,26],
    [194,24],
    [196,14],
    [197,17],
    [199,23],
    [201,24],
    [204,24],[204,25],
    [205,24],[205,25],
    [207,14],[207,22],
    [208,17],[208,27],
    [213,0],
    [214,35],
    [215,36],
    [224,35],
    [225,36],
    [226,23],[226,30],
    [228,24],[228,25],
    [232,24],[232,25],
    [233,11],
    [234,19],
    [235,21],
    [238,1],
    [239,14],
    [240,17],
    [241,0],
    [242,35],
    [243,36],
    [245,10],[245,14],[245,24],
    [246,24],
    [247,1],[247,14],[247,30],
    [249,10],[249,24],
    [250,10],[250,24],
    [251,4],[251,6],
    [252,7],
    [253,14],
    [254,35],
    [255,36],
    [256,35],
    [257,36],
    [258,11],
    [259,14],
    [260,17],
    [262,35],
    [263,36],
    [264,35],[264,37],
    [265,36],
    [266,32],
    [267,32],
    [270,15],
    [282,31],
    [285,3],[285,4],
    [301,3],[301,18],
    [305,3],[305,4],[305,5],
    [308,19],
    [309,19],
    [323,16],
    [336,3],[336,4],
    [338,19],[338,20],
    [340,19],
    [342,19],
    [359,17],
    [361,15],
    [366,14],[366,17],
    [376,14],
    [380,14],
    [381,14],
    [382,14],
    [391,14],
    [396,14],
    [404,14],
    [405,28],
    [409,2],[409,14],[409,28],
    [412,14],[412,17],
    [420,1],[420,15],
    [439,36],
    [441,14],
    [442,14],
    [443,17],
    [448,36],
    [449,36],
  ],
};
// END GENERATED DATA

type Status = "verified" | "conditional" | "partial" | "funspec" | "excluded";
const STATUS_ORDER: Status[] = ["verified", "conditional", "partial", "funspec", "excluded"];
const STATUS_LABEL: Record<Status, string> = {
  verified: "Sound and complete",
  conditional: "Sound and complete with a prior circuit",
  partial: "Constraints specified, proof partial",
  funspec: "Funspec only",
  excluded: "Excluded (hash internals)",
};
const FLAG_NAMES = ["FUN-SPEC", "R1CS-SPEC", "PFCS-SPEC", "R1CS-SAMPLES", "R1CS-SOUND", "R1CS-COMPLETE"];
const MONO = "ui-monospace, SFMono-Regular, Menlo, monospace";

type Fn = {
  i: number;
  crate: string;
  type: string;
  trait: string;
  fn: string;
  flags: string;
  soundIf: string;
  completeIf: string;
  loc: string;
  label: string;
  status: Status;
  tkey: string;
};

// Matches STATUS in the CSV: verified when soundness and completeness each hold outright or
// together with the prior circuit named in R1CS-SOUND-IF / R1CS-COMPLETE-IF.
function statusOf(flags: string, soundIf: string, completeIf: string): Status {
  if (flags[0] === "x") return "excluded";
  const sound = flags[4] === "1" || soundIf !== "";
  const complete = flags[5] === "1" || completeIf !== "";
  if (sound && complete) return soundIf || completeIf ? "conditional" : "verified";
  if (flags[1] === "1" || flags[2] === "1") return "partial";
  return "funspec";
}

function typeLabel(type: string): string {
  if (type === "<trait default>") return "default";
  return type;
}

const FNS: Fn[] = DATA.n.map(([crate, type, trait, fn, flags, soundIf, completeIf, loc], i) => {
  const t = typeLabel(type);
  return {
    i,
    crate,
    type,
    trait,
    fn,
    flags,
    soundIf,
    completeIf,
    loc,
    label: t ? `${t}::${fn}` : fn,
    status: statusOf(flags, soundIf, completeIf),
    tkey: `${crate}|${type}`,
  };
});

const CALLEES: number[][] = FNS.map(() => []);
const CALLERS: number[][] = FNS.map(() => []);
for (const [s, t] of DATA.e) {
  CALLEES[s].push(t);
  CALLERS[t].push(s);
}
const DISPATCH = DATA.d.map(([name, impls], j) => ({ j, name, impls }));
const D_OUT: number[][] = FNS.map(() => []);
const D_IN: number[][] = DISPATCH.map(() => []);
for (const [s, j] of DATA.de) {
  D_OUT[s].push(j);
  D_IN[j].push(s);
}

function closure(start: number[], adj: number[][]): Set<number> {
  const seen = new Set<number>();
  const stack = [...start];
  while (stack.length) {
    const v = stack.pop() as number;
    for (const w of adj[v]) {
      if (!seen.has(w)) {
        seen.add(w);
        stack.push(w);
      }
    }
  }
  return seen;
}

const DEPTH: number[] = (() => {
  const memo: number[] = FNS.map(() => 0);
  const go = (i: number): number => {
    if (memo[i]) return memo[i];
    let best = 0;
    for (const c of CALLEES[i]) best = Math.max(best, go(c));
    memo[i] = best + 1;
    return memo[i];
  };
  FNS.forEach((f) => go(f.i));
  return memo;
})();
const MAX_DEPTH = Math.max(...DEPTH);
const DEPENDENTS: number[] = FNS.map((f) => closure([f.i], CALLERS).size);

const STATUS_COUNT: Record<Status, number> = { verified: 0, conditional: 0, partial: 0, funspec: 0, excluded: 0 };
FNS.forEach((f) => (STATUS_COUNT[f.status] += 1));

const CRATES = Array.from(new Set(FNS.map((f) => f.crate))).sort();

type TypeNode = { key: string; crate: string; type: string; label: string; fns: number[]; counts: Record<Status, number> };
const TYPES: TypeNode[] = (() => {
  const m = new Map<string, TypeNode>();
  for (const f of FNS) {
    let t = m.get(f.tkey);
    if (!t) {
      t = {
        key: f.tkey,
        crate: f.crate,
        type: f.type,
        label: f.type === "" ? "free functions" : typeLabel(f.type),
        fns: [],
        counts: { verified: 0, conditional: 0, partial: 0, funspec: 0, excluded: 0 },
      };
      m.set(f.tkey, t);
    }
    t.fns.push(f.i);
    t.counts[f.status] += 1;
  }
  const all = Array.from(m.values());
  const seen = new Map<string, number>();
  all.forEach((t) => seen.set(t.label, (seen.get(t.label) || 0) + 1));
  all.forEach((t) => {
    if ((seen.get(t.label) || 0) > 1) t.label = `${t.label} (${t.crate.replace("types/", "")})`;
  });
  return all;
})();
const TYPE_EDGES: { from: string; to: string }[] = (() => {
  const s = new Set<string>();
  for (const [a, b] of DATA.e) {
    const ta = FNS[a].tkey;
    const tb = FNS[b].tkey;
    if (ta !== tb) s.add(`${tb}>${ta}`);
  }
  return Array.from(s).map((k) => {
    const [from, to] = k.split(">");
    return { from, to };
  });
})();

function statusColor(theme: CanvasHostTheme, s: Status): string {
  switch (s) {
    case "verified":
      return theme.category.green;
    case "conditional":
      return theme.category.blue;
    case "partial":
      return theme.category.yellow;
    case "funspec":
      return theme.text.tertiary;
    default:
      return theme.text.quaternary;
  }
}

function dispatchLabel(name: string): string {
  if (name.startsWith("op ")) return `operator ${name.slice(3)}`;
  if (name.includes("::")) return `${name}()`;
  return `.${name}()`;
}

function clip(s: string, n: number): string {
  return s.length > n ? s.slice(0, n - 1) + "…" : s;
}

type Sel = { kind: "f" | "d"; i: number } | null;
function parseSel(s: string | null): Sel {
  if (!s) return null;
  const i = Number(s.slice(1));
  if (s[0] === "f" && FNS[i]) return { kind: "f", i };
  if (s[0] === "d" && DISPATCH[i]) return { kind: "d", i };
  return null;
}

const NODE_W = 212;
const NODE_H = 18;
const TOP = 22;
type Stoppable = { stopPropagation: () => void };

function FunctionGraph(props: {
  visible: Set<number>;
  context: Set<number>;
  showDispatch: boolean;
  sel: Sel;
  matches: Set<number>;
  zoom: number;
  onSelect: (id: string | null) => void;
}) {
  const { visible, context, showDispatch, sel, matches, zoom, onSelect } = props;
  const theme = useHostTheme();

  const layout = useMemo(() => {
    const nodes: { id: string }[] = [];
    const edges: { from: string; to: string }[] = [];
    const dset = new Set<number>();
    visible.forEach((i) => {
      nodes.push({ id: "f" + i });
      for (const c of CALLEES[i]) if (visible.has(c)) edges.push({ from: "f" + c, to: "f" + i });
      if (showDispatch)
        for (const j of D_OUT[i]) {
          dset.add(j);
          edges.push({ from: "d" + j, to: "f" + i });
        }
    });
    dset.forEach((j) => nodes.push({ id: "d" + j }));
    return computeDAGLayout({
      nodes,
      edges,
      direction: "horizontal",
      nodeWidth: NODE_W,
      nodeHeight: NODE_H,
      rankGap: 64,
      nodeGap: 4,
      padding: 12,
    });
  }, [visible, showDispatch]);

  const hl = useMemo(() => {
    if (!sel) return null;
    const nodes = new Set<string>();
    const edges = new Set<string>();
    if (sel.kind === "f") {
      const s = sel.i;
      const down = closure([s], CALLEES);
      const up = closure([s], CALLERS);
      nodes.add("f" + s);
      down.forEach((v) => nodes.add("f" + v));
      up.forEach((v) => nodes.add("f" + v));
      const lower = new Set<number>([s, ...down]);
      const upper = new Set<number>([s, ...up]);
      lower.forEach((p) => {
        for (const c of CALLEES[p]) edges.add(`f${c}>f${p}`);
        for (const j of D_OUT[p]) {
          nodes.add("d" + j);
          edges.add(`d${j}>f${p}`);
        }
      });
      upper.forEach((c) => {
        for (const p of CALLERS[c]) edges.add(`f${c}>f${p}`);
      });
    } else {
      const j = sel.i;
      nodes.add("d" + j);
      for (const p of D_IN[j]) {
        nodes.add("f" + p);
        edges.add(`d${j}>f${p}`);
      }
      for (const k of DISPATCH[j].impls) nodes.add("f" + k);
    }
    return { nodes, edges };
  }, [sel]);

  const selId = sel ? sel.kind + sel.i : null;
  const pos = new Map(layout.nodes.map((n) => [n.id, n]));
  const W = layout.width;
  const H = layout.height + TOP;

  return (
    <div
      style={{
        overflow: "auto",
        maxHeight: 780,
        border: `1px solid ${theme.stroke.tertiary}`,
        borderRadius: 6,
        background: theme.bg.editor,
      }}
    >
      <svg
        width={W * zoom}
        height={H * zoom}
        viewBox={`0 0 ${W} ${H}`}
        style={{ display: "block" }}
        onClick={() => onSelect(null)}
      >
        {layout.ranks.map((r) => (
          <text
            key={r.rank}
            x={r.x + NODE_W / 2}
            y={14}
            textAnchor="middle"
            fontSize={10}
            fill={theme.text.tertiary}
          >
            {`level ${r.rank} · ${r.nodeIds.length}`}
          </text>
        ))}
        <g transform={`translate(0, ${TOP})`}>
          {layout.edges.map((e) => {
            const k = `${e.from}>${e.to}`;
            const on = hl ? hl.edges.has(k) : false;
            const dx = Math.max(24, (e.targetX - e.sourceX) * 0.4);
            return (
              <path
                key={k}
                d={`M${e.sourceX},${e.sourceY} C${e.sourceX + dx},${e.sourceY} ${e.targetX - dx},${e.targetY} ${e.targetX},${e.targetY}`}
                fill="none"
                stroke={on ? theme.accent.primary : theme.stroke.primary}
                strokeWidth={on ? 1.4 : 0.8}
                strokeOpacity={hl ? (on ? 0.95 : 0.12) : 0.55}
                strokeDasharray={e.from[0] === "d" || e.isBackEdge ? "3 3" : undefined}
              />
            );
          })}
          {layout.nodes.map((n) => {
            const isSel = n.id === selId;
            const dim = hl ? !hl.nodes.has(n.id) : false;
            const idx = Number(n.id.slice(1));
            if (n.id[0] === "d") {
              const d = DISPATCH[idx];
              return (
                <g
                  key={n.id}
                  transform={`translate(${n.x},${n.y})`}
                  opacity={dim ? 0.25 : 1}
                  style={{ cursor: "pointer" }}
                  onClick={(ev: Stoppable) => {
                    ev.stopPropagation();
                    onSelect(n.id);
                  }}
                >
                  <title>{`${dispatchLabel(d.name)}: resolved by name only, ${d.impls.length} candidate implementations`}</title>
                  <rect
                    width={NODE_W}
                    height={NODE_H}
                    rx={9}
                    fill={theme.bg.editor}
                    stroke={isSel ? theme.accent.primary : theme.stroke.primary}
                    strokeWidth={isSel ? 2 : 1}
                    strokeDasharray="3 2"
                  />
                  <text
                    x={9}
                    y={NODE_H / 2}
                    dominantBaseline="central"
                    fontSize={10.5}
                    fontFamily={MONO}
                    fontStyle="italic"
                    fill={theme.text.secondary}
                  >
                    {clip(`${dispatchLabel(d.name)} ×${d.impls.length}`, 31)}
                  </text>
                </g>
              );
            }
            const f = FNS[idx];
            const color = statusColor(theme, f.status);
            const isMatch = matches.has(idx);
            return (
              <g
                key={n.id}
                transform={`translate(${n.x},${n.y})`}
                opacity={dim ? 0.22 : 1}
                style={{ cursor: "pointer" }}
                onClick={(ev: Stoppable) => {
                  ev.stopPropagation();
                  onSelect(n.id);
                }}
              >
                <title>{`${f.label}${f.trait ? ` (${f.trait})` : ""} · ${f.crate} · ${STATUS_LABEL[f.status]}`}</title>
                <rect
                  width={NODE_W}
                  height={NODE_H}
                  rx={3}
                  fill={color}
                  fillOpacity={f.status === "funspec" || f.status === "excluded" ? 0.08 : 0.2}
                  stroke={isSel || isMatch ? theme.accent.primary : theme.stroke.tertiary}
                  strokeWidth={isSel ? 2 : isMatch ? 1.5 : 1}
                  strokeDasharray={f.status === "excluded" ? "3 2" : undefined}
                />
                <rect width={3} height={NODE_H} fill={color} />
                <text
                  x={8}
                  y={NODE_H / 2}
                  dominantBaseline="central"
                  fontSize={10.5}
                  fontFamily={MONO}
                  fill={context.has(idx) ? theme.text.tertiary : theme.text.primary}
                >
                  {clip(f.label, 31)}
                </text>
              </g>
            );
          })}
        </g>
      </svg>
    </div>
  );
}

function TypeGraph(props: { zoom: number; onPick: (key: string) => void }) {
  const { zoom, onPick } = props;
  const theme = useHostTheme();
  const TW = 176;
  const TH = 40;
  const layout = useMemo(
    () =>
      computeDAGLayout({
        nodes: TYPES.map((t) => ({ id: t.key })),
        edges: TYPE_EDGES,
        direction: "horizontal",
        nodeWidth: TW,
        nodeHeight: TH,
        rankGap: 72,
        nodeGap: 8,
        padding: 12,
      }),
    [],
  );
  const byKey = new Map(TYPES.map((t) => [t.key, t]));
  const W = layout.width;
  const H = layout.height + TOP;
  return (
    <div
      style={{
        overflow: "auto",
        maxHeight: 780,
        border: `1px solid ${theme.stroke.tertiary}`,
        borderRadius: 6,
        background: theme.bg.editor,
      }}
    >
      <svg width={W * zoom} height={H * zoom} viewBox={`0 0 ${W} ${H}`} style={{ display: "block" }}>
        {layout.ranks.map((r) => (
          <text key={r.rank} x={r.x + TW / 2} y={14} textAnchor="middle" fontSize={10} fill={theme.text.tertiary}>
            {`level ${r.rank}`}
          </text>
        ))}
        <g transform={`translate(0, ${TOP})`}>
          {layout.edges.map((e) => {
            const dx = Math.max(24, (e.targetX - e.sourceX) * 0.4);
            return (
              <path
                key={`${e.from}>${e.to}`}
                d={`M${e.sourceX},${e.sourceY} C${e.sourceX + dx},${e.sourceY} ${e.targetX - dx},${e.targetY} ${e.targetX},${e.targetY}`}
                fill="none"
                stroke={theme.stroke.primary}
                strokeWidth={0.9}
                strokeOpacity={0.6}
                strokeDasharray={e.isBackEdge ? "3 3" : undefined}
              />
            );
          })}
          {layout.nodes.map((n) => {
            const t = byKey.get(n.id) as TypeNode;
            let x = 0;
            const barW = TW - 16;
            return (
              <g
                key={n.id}
                transform={`translate(${n.x},${n.y})`}
                style={{ cursor: "pointer" }}
                onClick={() => onPick(t.key)}
              >
                <title>{`${t.label} · ${t.crate} · ${t.fns.length} functions. Click to open its call graph.`}</title>
                <rect width={TW} height={TH} rx={4} fill={theme.bg.editor} stroke={theme.stroke.secondary} />
                <text x={8} y={15} fontSize={11} fontWeight={600} fontFamily={MONO} fill={theme.text.primary}>
                  {clip(t.label, 18)}
                </text>
                <text x={TW - 8} y={15} fontSize={10} textAnchor="end" fill={theme.text.tertiary}>
                  {t.fns.length}
                </text>
                {STATUS_ORDER.map((s) => {
                  const w = (t.counts[s] / t.fns.length) * barW;
                  const r = <rect key={s} x={8 + x} y={26} width={w} height={5} fill={statusColor(theme, s)} />;
                  x += w;
                  return r;
                })}
              </g>
            );
          })}
        </g>
      </svg>
    </div>
  );
}

function FnRow(props: { i: number; onSelect: (id: string) => void; right?: string }) {
  const theme = useHostTheme();
  const f = FNS[props.i];
  return (
    <div
      onClick={() => props.onSelect("f" + props.i)}
      title={`${f.label}${f.trait ? ` (${f.trait})` : ""} · ${f.crate}`}
      style={{ display: "flex", alignItems: "center", gap: 6, padding: "2px 0", cursor: "pointer" }}
    >
      <span
        style={{ width: 8, height: 8, borderRadius: 2, background: statusColor(theme, f.status), flex: "none" }}
      />
      <span
        style={{
          fontFamily: MONO,
          fontSize: 11.5,
          color: theme.text.primary,
          overflow: "hidden",
          textOverflow: "ellipsis",
          whiteSpace: "nowrap",
          flex: 1,
          minWidth: 0,
        }}
      >
        {f.label}
      </span>
      {props.right ? <span style={{ fontSize: 11, color: theme.text.tertiary }}>{props.right}</span> : null}
    </div>
  );
}

function ListBlock(props: { title: string; ids: number[]; onSelect: (id: string) => void; right?: (i: number) => string }) {
  if (!props.ids.length) return null;
  return (
    <Stack gap={4}>
      <Text size="small" weight="semibold" tone="secondary">
        {`${props.title} (${props.ids.length})`}
      </Text>
      <div style={{ maxHeight: 220, overflow: "auto" }}>
        {props.ids.map((i) => (
          <FnRow key={i} i={i} onSelect={props.onSelect} right={props.right ? props.right(i) : undefined} />
        ))}
      </div>
    </Stack>
  );
}

function Inspector(props: { sel: Sel; onSelect: (id: string) => void }) {
  const { sel, onSelect } = props;
  const theme = useHostTheme();
  const byLabel = (a: number, b: number) => FNS[a].label.localeCompare(FNS[b].label);

  if (!sel) {
    const hubs = FNS.map((f) => f.i)
      .sort((a, b) => DEPENDENTS[b] - DEPENDENTS[a])
      .slice(0, 12);
    const deep = FNS.map((f) => f.i)
      .sort((a, b) => DEPTH[b] - DEPTH[a] || byLabel(a, b))
      .slice(0, 8);
    return (
      <Stack gap={14}>
        <Text size="small" tone="secondary">
          Click a function to trace what it calls and what calls it.
        </Text>
        <ListBlock
          title="Most depended-on"
          ids={hubs}
          onSelect={onSelect}
          right={(i) => `${DEPENDENTS[i]} callers`}
        />
        <ListBlock title="Longest call chains" ids={deep} onSelect={onSelect} right={(i) => `${DEPTH[i]} deep`} />
      </Stack>
    );
  }

  if (sel.kind === "d") {
    const d = DISPATCH[sel.i];
    return (
      <Stack gap={12}>
        <Stack gap={2}>
          <H3>{dispatchLabel(d.name)}</H3>
          <Text size="small" tone="secondary">
            The scanner matched this call by name only, so the callee is one of these implementations.
          </Text>
        </Stack>
        <ListBlock title="Called from" ids={[...D_IN[sel.i]].sort(byLabel)} onSelect={onSelect} />
        <ListBlock title="Candidate implementations" ids={[...d.impls].sort(byLabel)} onSelect={onSelect} />
      </Stack>
    );
  }

  const f = FNS[sel.i];
  const down = closure([f.i], CALLEES).size;
  const up = DEPENDENTS[f.i];
  return (
    <Stack gap={12}>
      <Stack gap={2}>
        <div style={{ fontFamily: MONO, fontSize: 14, fontWeight: 600, color: theme.text.primary, wordBreak: "break-all" }}>
          {f.label}
        </div>
        <Text size="small" tone="secondary">
          {`${f.crate}${f.trait ? ` · trait ${f.trait}` : ""}`}
        </Text>
        <Text size="small" tone="tertiary">
          <Code>{f.loc}</Code>
        </Text>
      </Stack>
      <Row gap={6} align="center">
        <span style={{ width: 10, height: 10, borderRadius: 2, background: statusColor(theme, f.status) }} />
        <Text size="small" weight="medium">
          {STATUS_LABEL[f.status]}
        </Text>
      </Row>
      <div style={{ display: "grid", gridTemplateColumns: "1fr auto", rowGap: 2, columnGap: 12 }}>
        {FLAG_NAMES.map((name, k) => {
          const v = f.flags[k];
          return [
            <span key={name} style={{ fontFamily: MONO, fontSize: 11, color: theme.text.secondary }}>
              {name}
            </span>,
            <span
              key={name + "v"}
              style={{
                fontFamily: MONO,
                fontSize: 11,
                color: v === "1" ? theme.category.green : theme.text.tertiary,
                textAlign: "right",
              }}
            >
              {v === "x" ? "excluded" : v}
            </span>,
          ];
        })}
      </div>
      {f.soundIf ? (
        <Text size="small" tone="secondary">
          {"Sound together with: "}
          <Code>{f.soundIf}</Code>
        </Text>
      ) : null}
      {f.completeIf ? (
        <Text size="small" tone="secondary">
          {"Complete together with: "}
          <Code>{f.completeIf}</Code>
        </Text>
      ) : null}
      <Text size="small" tone="tertiary">
        {`${DEPTH[f.i]} levels deep · reaches ${down} functions · reached from ${up}`}
      </Text>
      <Divider />
      <ListBlock title="Calls" ids={[...CALLEES[f.i]].sort(byLabel)} onSelect={onSelect} />
      {D_OUT[f.i].length ? (
        <Stack gap={4}>
          <Text size="small" weight="semibold" tone="secondary">
            {`Calls matched by name only (${D_OUT[f.i].length})`}
          </Text>
          {D_OUT[f.i].map((j) => (
            <div
              key={j}
              onClick={() => onSelect("d" + j)}
              style={{ fontFamily: MONO, fontSize: 11.5, color: theme.text.secondary, cursor: "pointer", padding: "1px 0" }}
            >
              {`${dispatchLabel(DISPATCH[j].name)}  ·  ${DISPATCH[j].impls.length} candidates`}
            </div>
          ))}
        </Stack>
      ) : null}
      <ListBlock title="Called by" ids={[...CALLERS[f.i]].sort(byLabel)} onSelect={onSelect} />
    </Stack>
  );
}

export default function CircuitCallGraph() {
  const theme = useHostTheme();
  const [view, setView] = useCanvasState<string>("view", "functions");
  const [scope, setScope] = useCanvasState<string>("scope", "all");
  const [selRaw, setSelRaw] = useCanvasState<string | null>("sel", null);
  const [showDispatch, setShowDispatch] = useCanvasState<boolean>("dispatch", false);
  const [focus, setFocus] = useCanvasState<boolean>("focus", false);
  const [zoom, setZoom] = useCanvasState<string>("zoom", "0.8");
  const [query, setQuery] = useState("");
  const sel = parseSel(selRaw);

  const { visible, context } = useMemo(() => {
    if (focus && sel && sel.kind === "f") {
      const set = new Set<number>([sel.i, ...closure([sel.i], CALLEES), ...closure([sel.i], CALLERS)]);
      return { visible: set, context: new Set<number>() };
    }
    if (focus && sel && sel.kind === "d") {
      const set = new Set<number>([...D_IN[sel.i], ...DISPATCH[sel.i].impls]);
      return { visible: set, context: new Set<number>() };
    }
    const inScope = (f: Fn) =>
      scope === "all" ||
      (scope.startsWith("crate:") && f.crate === scope.slice(6)) ||
      (scope.startsWith("type:") && f.tkey === scope.slice(5));
    const base = FNS.filter(inScope).map((f) => f.i);
    const extra = closure(base, CALLEES);
    const baseSet = new Set(base);
    const ctx = new Set<number>();
    extra.forEach((v) => {
      if (!baseSet.has(v)) ctx.add(v);
    });
    return { visible: new Set<number>([...base, ...extra]), context: ctx };
  }, [scope, focus, selRaw]);

  const matches = useMemo(() => {
    const q = query.trim().toLowerCase();
    if (q.length < 2) return [] as number[];
    return FNS.filter((f) => f.label.toLowerCase().includes(q) || f.crate.includes(q)).map((f) => f.i);
  }, [query]);
  const matchSet = useMemo(() => new Set(matches), [matches]);

  const scopeOptions = [
    { value: "all", label: `All crates (${FNS.length})` },
    ...CRATES.map((c) => ({ value: `crate:${c}`, label: `${c} (${FNS.filter((f) => f.crate === c).length})` })),
  ];
  if (scope.startsWith("type:")) {
    const t = TYPES.find((x) => x.key === scope.slice(5));
    if (t) scopeOptions.push({ value: scope, label: `Type ${t.label} (${t.fns.length})` });
  }

  const select = (id: string | null) => setSelRaw(id);
  const nameOnlyCalls = DATA.de.length;
  const done = STATUS_COUNT.verified + STATUS_COUNT.conditional;

  return (
    <Stack gap={18} style={{ padding: 4 }}>
      <Stack gap={6}>
        <H1>AleoVM circuit call graph</H1>
        <Text tone="secondary">
          Every constraint-generating function in snarkVM's <Code>circuit/</Code> tree, laid out by how many calls separate it
          from the bottom. Level 0 holds functions that call no other circuit function; each line joins a function on the
          right to a function it calls on the left.
        </Text>
      </Stack>

      <Row gap={32} wrap>
        <Stat value={FNS.length} label="Circuit functions" />
        <Stat value={DATA.e.length} label="Resolved calls" />
        <Stat value={nameOnlyCalls} label="Calls matched by name only" tone="warning" />
        <Stat value={MAX_DEPTH} label="Longest call chain" />
        <Stat value={done} label="Sound and complete" tone="success" />
      </Row>

      <Row gap={10} align="center" wrap>
        <Pill active={view === "functions"} onClick={() => setView("functions")}>
          Functions
        </Pill>
        <Pill active={view === "types"} onClick={() => setView("types")}>
          Types
        </Pill>
        <div style={{ width: 1, height: 20, background: theme.stroke.secondary }} />
        {view === "functions" ? (
          <>
            <Select value={scope} onChange={(v) => setScope(v)} options={scopeOptions} style={{ minWidth: 190 }} />
            <TextInput value={query} onChange={setQuery} placeholder="Search functions…" type="search" style={{ width: 200 }} />
            <Row gap={6} align="center">
              <Toggle checked={showDispatch} onChange={setShowDispatch} />
              <Text size="small" tone="secondary">
                Name-only calls
              </Text>
            </Row>
            <Row gap={6} align="center">
              <Toggle checked={focus} onChange={setFocus} />
              <Text size="small" tone="secondary">
                Only the selection's callers and callees
              </Text>
            </Row>
          </>
        ) : (
          <Text size="small" tone="secondary">
            Click a type to open its functions and everything they call.
          </Text>
        )}
        <Select
          value={zoom}
          onChange={setZoom}
          options={[
            { value: "0.5", label: "50%" },
            { value: "0.65", label: "65%" },
            { value: "0.8", label: "80%" },
            { value: "1", label: "100%" },
          ]}
          style={{ width: 84 }}
        />
      </Row>

      {view === "functions" && matches.length ? (
        <Row gap={6} wrap>
          {matches.slice(0, 14).map((i) => (
            <Pill key={i} size="sm" active={selRaw === "f" + i} onClick={() => select("f" + i)}>
              {FNS[i].label}
            </Pill>
          ))}
          {matches.length > 14 ? (
            <Text size="small" tone="tertiary">{`+${matches.length - 14} more`}</Text>
          ) : null}
        </Row>
      ) : null}

      <Row gap={16} wrap>
        {STATUS_ORDER.map((s) => (
          <Row key={s} gap={6} align="center">
            <span style={{ width: 10, height: 10, borderRadius: 2, background: statusColor(theme, s) }} />
            <Text size="small" tone="secondary">{`${STATUS_LABEL[s]} · ${STATUS_COUNT[s]}`}</Text>
          </Row>
        ))}
        {view === "functions" && showDispatch ? (
          <Row gap={6} align="center">
            <span style={{ width: 16, height: 10, borderRadius: 5, border: `1px dashed ${theme.stroke.primary}` }} />
            <Text size="small" tone="secondary">Name-only call (one of several implementations)</Text>
          </Row>
        ) : null}
      </Row>

      {view === "functions" ? (
        <Grid columns="minmax(0, 1fr) 320px" gap={16} align="start">
          <Stack gap={6}>
            <FunctionGraph
              visible={visible}
              context={context}
              showDispatch={showDispatch}
              sel={sel}
              matches={matchSet}
              zoom={Number(zoom)}
              onSelect={select}
            />
            <Text size="small" tone="tertiary">
              {`${visible.size} functions shown.${
                context.size ? ` ${context.size} grey labels are callees outside the selected scope.` : ""
              } Click the background to clear the selection.`}
            </Text>
          </Stack>
          <div style={{ position: "sticky", top: 8 }}>
            <Inspector sel={sel} onSelect={select} />
          </div>
        </Grid>
      ) : (
        <Stack gap={6}>
          <TypeGraph
            zoom={Number(zoom)}
            onPick={(key) => {
              setScope(`type:${key}`);
              setSelRaw(null);
              setFocus(false);
              setView("functions");
            }}
          />
          <Text size="small" tone="tertiary">
            {`${TYPES.length} types, ${TYPE_EDGES.length} type-to-type call links. The bar under each type splits its functions by proof status.`}
          </Text>
        </Stack>
      )}

      <Callout tone="neutral" title="How calls were resolved">
        The scanner reads Rust bodies without type inference. A call counts as resolved when it is a typed path such as{" "}
        <Code>Group::ternary</Code>, a call on <Code>self</Code> or on a struct field whose type is declared, an operator on the
        function's own type, or a name with a single implementation. The other {nameOnlyCalls} calls, for example{" "}
        <Code>bits.write_bits_le()</Code> on a local variable, could reach several implementations; turn on name-only calls to see
        them as dashed nodes. A <Code>*_assign</Code> function is never drawn as calling its own operator: the arithmetic
        inside it acts on linear combinations, and the operator itself calls <Code>*_assign</Code>.
      </Callout>

      <Text size="small" tone="tertiary">
        Source: snarkVM <Code>circuit/</Code> at 7dc117d45 (2026-10-14) and{" "}
        <Code>aleovm_circuit_function_formalisation_status.csv</Code>, generated by <Code>aleovm_circuit_call_graph.py</Code>.
      </Text>
    </Stack>
  );
}
