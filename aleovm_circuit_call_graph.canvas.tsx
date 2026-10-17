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
    ["account","ComputeKey","","to_address","100000","","","account/src/compute_key/to_address.rs:20"],
    ["account","ComputeKey","Equal","is_equal","110100","","","account/src/compute_key/equal.rs:24"],
    ["account","ComputeKey","Equal","is_not_equal","110100","","","account/src/compute_key/equal.rs:42"],
    ["account","ComputeKey","From","from","110101","","","account/src/compute_key/from.rs:20"],
    ["account","ComputeKey","FromBits","from_bits_be","100000","","","account/src/compute_key/helpers/from_bits.rs:39"],
    ["account","ComputeKey","FromBits","from_bits_le","100000","","","account/src/compute_key/helpers/from_bits.rs:22"],
    ["account","ComputeKey","Inject","new","100000","","","account/src/compute_key/mod.rs:44"],
    ["account","ComputeKey","Ternary","ternary","111101","","","account/src/compute_key/ternary.rs:23"],
    ["account","ComputeKey","ToBits","write_bits_be","100000","","","account/src/compute_key/helpers/to_bits.rs:27"],
    ["account","ComputeKey","ToBits","write_bits_le","100000","","","account/src/compute_key/helpers/to_bits.rs:22"],
    ["account","ComputeKey","ToFields","to_fields","111111","","","account/src/compute_key/helpers/to_fields.rs:22"],
    ["account","PrivateKey","","to_compute_key","100000","","","account/src/private_key/to_compute_key.rs:20"],
    ["account","PrivateKey","","to_view_key","100000","","","account/src/private_key/to_view_key.rs:20"],
    ["account","Signature","","verify","100000","","","account/src/signature/verify.rs:20"],
    ["account","Signature","Equal","is_equal","110000","","","account/src/signature/equal.rs:24"],
    ["account","Signature","Equal","is_not_equal","110000","","","account/src/signature/equal.rs:42"],
    ["account","Signature","FromBits","from_bits_be","100000","","","account/src/signature/helpers/from_bits.rs:48"],
    ["account","Signature","FromBits","from_bits_le","100000","","","account/src/signature/helpers/from_bits.rs:22"],
    ["account","Signature","Inject","new","100000","","","account/src/signature/mod.rs:42"],
    ["account","Signature","Ternary","ternary","111100","","","account/src/signature/ternary.rs:23"],
    ["account","Signature","ToBits","write_bits_be","100000","","","account/src/signature/helpers/to_bits.rs:27"],
    ["account","Signature","ToBits","write_bits_le","100000","","","account/src/signature/helpers/to_bits.rs:22"],
    ["account","Signature","ToFields","to_fields","111111","","","account/src/signature/helpers/to_fields.rs:22"],
    ["account","ViewKey","","from_private_key","100000","","","account/src/view_key/from_private_key.rs:20"],
    ["account","ViewKey","","to_address","100000","","","account/src/view_key/to_address.rs:20"],
    ["algorithms","BHP","Commit","commit","x00000","","","algorithms/src/bhp/commit.rs:24"],
    ["algorithms","BHP","CommitUncompressed","commit_uncompressed","x00000","","","algorithms/src/bhp/commit_uncompressed.rs:26"],
    ["algorithms","BHP","HashUncompressed","hash_uncompressed","x00000","","","algorithms/src/bhp/hash_uncompressed.rs:28"],
    ["algorithms","BHPHasher","HashUncompressed","hash_uncompressed","x00000","","","algorithms/src/bhp/hasher/hash_uncompressed.rs:30"],
    ["algorithms","BHPHasher","Inject","new","x00000","","","algorithms/src/bhp/hasher/mod.rs:63"],
    ["algorithms","Elligator2","","encode","x00000","","","algorithms/src/elligator2/encode.rs:21"],
    ["algorithms","Keccak","","pad_keccak","x00000","","","algorithms/src/keccak/hash.rs:92"],
    ["algorithms","Keccak","","pad_sha3","x00000","","","algorithms/src/keccak/hash.rs:122"],
    ["algorithms","Keccak","","permutation_f","x00000","","","algorithms/src/keccak/hash.rs:156"],
    ["algorithms","Keccak","","rotate_left","x00000","","","algorithms/src/keccak/hash.rs:276"],
    ["algorithms","Keccak","","round","x00000","","","algorithms/src/keccak/hash.rs:185"],
    ["algorithms","Pedersen","Commit","commit","x00000","","","algorithms/src/pedersen/commit.rs:24"],
    ["algorithms","Pedersen","CommitUncompressed","commit_uncompressed","x00000","","","algorithms/src/pedersen/commit_uncompressed.rs:24"],
    ["algorithms","Pedersen","HashUncompressed","hash_uncompressed","x00000","","","algorithms/src/pedersen/hash_uncompressed.rs:25"],
    ["algorithms","Poseidon","","absorb","x00000","","","algorithms/src/poseidon/hash_many.rs:45"],
    ["algorithms","Poseidon","","apply_ark","x00000","","","algorithms/src/poseidon/hash_many.rs:145"],
    ["algorithms","Poseidon","","apply_mds","x00000","","","algorithms/src/poseidon/hash_many.rs:167"],
    ["algorithms","Poseidon","","apply_s_box","x00000","","","algorithms/src/poseidon/hash_many.rs:153"],
    ["algorithms","Poseidon","","permute","x00000","","","algorithms/src/poseidon/hash_many.rs:181"],
    ["algorithms","Poseidon","","squeeze","x00000","","","algorithms/src/poseidon/hash_many.rs:91"],
    ["algorithms","Poseidon","","squeeze_internal","x00000","","","algorithms/src/poseidon/hash_many.rs:101"],
    ["algorithms","Poseidon","HashMany","hash_many","x00000","","","algorithms/src/poseidon/hash_many.rs:23"],
    ["algorithms","Poseidon","HashToGroup","hash_to_group","x00000","","","algorithms/src/poseidon/hash_to_group.rs:25"],
    ["algorithms","Poseidon","HashToScalar","hash_to_scalar","x00000","","","algorithms/src/poseidon/hash_to_scalar.rs:25"],
    ["algorithms","Poseidon","Inject","new","x00000","","","algorithms/src/poseidon/mod.rs:74"],
    ["collections","<trait default>","PathHash","hash_empty","100000","","","collections/src/kary_merkle_tree/helpers/path_hash.rs:33"],
    ["collections","BHP","PathHash","hash_children","100000","","","collections/src/kary_merkle_tree/helpers/path_hash.rs:44"],
    ["collections","BooleanHash","Equal","is_equal","111101","","","collections/src/kary_merkle_tree/helpers/mod.rs:68"],
    ["collections","BooleanHash","Equal","is_not_equal","111101","","","collections/src/kary_merkle_tree/helpers/mod.rs:73"],
    ["collections","BooleanHash","Inject","new","111111","","","collections/src/kary_merkle_tree/helpers/mod.rs:38"],
    ["collections","BooleanHash","Ternary","ternary","111101","","","collections/src/kary_merkle_tree/helpers/mod.rs:83"],
    ["collections","KaryMerklePath","","verify","111100","","","collections/src/kary_merkle_tree/verify.rs:21"],
    ["collections","KaryMerklePath","Inject","new","100100","","","collections/src/kary_merkle_tree/mod.rs:37"],
    ["collections","Keccak","PathHash","hash_children","100000","","","collections/src/kary_merkle_tree/helpers/path_hash.rs:78"],
    ["collections","MerklePath","","verify","111100","","","collections/src/merkle_tree/verify.rs:21"],
    ["collections","MerkleTree","","new","111101","","","collections/src/merkle_tree/mod.rs:110"],
    ["environment","","","recursively_replace_self","110101","","","environment/witness/src/lib.rs:20"],
    ["environment","","","rename_selfs","110101","","","environment/witness/src/lib.rs:40"],
    ["environment","(t0,ty,*)","Inject","new","100000","","","environment/src/traits/inject.rs:77"],
    ["environment","(t0,ty,+)","ToBits","write_bits_be","100000","","","environment/src/traits/to_bits.rs:195"],
    ["environment","(t0,ty,+)","ToBits","write_bits_le","100000","","","environment/src/traits/to_bits.rs:188"],
    ["environment","(t0,ty,+)","ToBitsRaw","write_bits_raw_be","100000","","","environment/src/traits/to_bits.rs:231"],
    ["environment","(t0,ty,+)","ToBitsRaw","write_bits_raw_le","100000","","","environment/src/traits/to_bits.rs:224"],
    ["environment","<trait default>","Environment","assert","111111","","","environment/src/environment.rs:73"],
    ["environment","<trait default>","Environment","assert_eq","111111","","","environment/src/environment.rs:80"],
    ["environment","<trait default>","Environment","assert_neq","111111","","","environment/src/environment.rs:89"],
    ["environment","<trait default>","ToBits","to_bits_be","100000","","","environment/src/traits/to_bits.rs:32"],
    ["environment","<trait default>","ToBits","to_bits_le","100000","","","environment/src/traits/to_bits.rs:23"],
    ["environment","<trait default>","ToBitsRaw","to_bits_raw_be","100000","","","environment/src/traits/to_bits.rs:53"],
    ["environment","<trait default>","ToBitsRaw","to_bits_raw_le","100000","","","environment/src/traits/to_bits.rs:44"],
    ["environment","CanaryCircuit","Environment","enforce","111111","","","environment/src/canary_circuit.rs:128"],
    ["environment","Circuit","Environment","enforce","111111","","","environment/src/circuit.rs:152"],
    ["environment","TestnetCircuit","Environment","enforce","111111","","","environment/src/testnet_circuit.rs:128"],
    ["environment","Vec","Inject","new","100000","","","environment/src/traits/inject.rs:61"],
    ["environment","Vec","ToBits","write_bits_be","100000","","","environment/src/traits/to_bits.rs:78"],
    ["environment","Vec","ToBits","write_bits_le","100000","","","environment/src/traits/to_bits.rs:71"],
    ["environment","Vec","ToBitsRaw","write_bits_raw_be","100000","","","environment/src/traits/to_bits.rs:134"],
    ["environment","Vec","ToBitsRaw","write_bits_raw_le","100000","","","environment/src/traits/to_bits.rs:127"],
    ["environment","[C]","ToBits","write_bits_be","100000","","","environment/src/traits/to_bits.rs:96"],
    ["environment","[C]","ToBits","write_bits_le","100000","","","environment/src/traits/to_bits.rs:89"],
    ["environment","[C]","ToBitsRaw","write_bits_raw_be","100000","","","environment/src/traits/to_bits.rs:150"],
    ["environment","[C]","ToBitsRaw","write_bits_raw_le","100000","","","environment/src/traits/to_bits.rs:143"],
    ["network","AleoV0","Aleo","commit_bhp1024","100000","","","network/src/v0.rs:183"],
    ["network","AleoV0","Aleo","commit_bhp256","100000","","","network/src/v0.rs:168"],
    ["network","AleoV0","Aleo","commit_bhp512","100000","","","network/src/v0.rs:173"],
    ["network","AleoV0","Aleo","commit_bhp768","100000","","","network/src/v0.rs:178"],
    ["network","AleoV0","Aleo","commit_ped128","100000","","","network/src/v0.rs:193"],
    ["network","AleoV0","Aleo","commit_ped64","100000","","","network/src/v0.rs:188"],
    ["network","AleoV0","Aleo","commit_to_group_bhp1024","100000","","","network/src/v0.rs:213"],
    ["network","AleoV0","Aleo","commit_to_group_bhp256","100000","","","network/src/v0.rs:198"],
    ["network","AleoV0","Aleo","commit_to_group_bhp512","100000","","","network/src/v0.rs:203"],
    ["network","AleoV0","Aleo","commit_to_group_bhp768","100000","","","network/src/v0.rs:208"],
    ["network","AleoV0","Aleo","commit_to_group_ped128","100000","","","network/src/v0.rs:223"],
    ["network","AleoV0","Aleo","commit_to_group_ped64","100000","","","network/src/v0.rs:218"],
    ["network","AleoV0","Aleo","g_scalar_multiply","111100","","","network/src/v0.rs:158"],
    ["network","AleoV0","Aleo","hash_many_psd2","100000","","","network/src/v0.rs:303"],
    ["network","AleoV0","Aleo","hash_many_psd4","100000","","","network/src/v0.rs:308"],
    ["network","AleoV0","Aleo","hash_many_psd8","100000","","","network/src/v0.rs:313"],
    ["network","AleoV0","Aleo","hash_to_group_bhp1024","100000","","","network/src/v0.rs:333"],
    ["network","AleoV0","Aleo","hash_to_group_bhp256","100000","","","network/src/v0.rs:318"],
    ["network","AleoV0","Aleo","hash_to_group_bhp512","100000","","","network/src/v0.rs:323"],
    ["network","AleoV0","Aleo","hash_to_group_bhp768","100000","","","network/src/v0.rs:328"],
    ["network","AleoV0","Aleo","hash_to_group_ped128","100000","","","network/src/v0.rs:343"],
    ["network","AleoV0","Aleo","hash_to_group_ped64","100000","","","network/src/v0.rs:338"],
    ["network","AleoV0","Aleo","hash_to_group_psd2","100000","","","network/src/v0.rs:348"],
    ["network","AleoV0","Aleo","hash_to_group_psd4","100000","","","network/src/v0.rs:353"],
    ["network","AleoV0","Aleo","hash_to_group_psd8","100000","","","network/src/v0.rs:358"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd2","100000","","","network/src/v0.rs:363"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd4","100000","","","network/src/v0.rs:368"],
    ["network","AleoV0","Aleo","hash_to_scalar_psd8","100000","","","network/src/v0.rs:373"],
    ["network","AleoV0","Aleo","verify_merkle_path_bhp","111100","","","network/src/v0.rs:378"],
    ["network","AleoV0","Aleo","verify_merkle_path_psd","111100","","","network/src/v0.rs:387"],
    ["network","AleoV0","Environment","enforce","111111","","","network/src/v0.rs:431"],
    ["program","","","compute_function_id","100000","","","program/src/function_id/mod.rs:21"],
    ["program","Argument","Equal","is_equal","100000","","","program/src/data/future/argument.rs:68"],
    ["program","Argument","Equal","is_not_equal","100000","","","program/src/data/future/argument.rs:78"],
    ["program","Argument","Inject","new","100000","","","program/src/data/future/argument.rs:33"],
    ["program","Argument","ToBits","write_bits_be","100000","","","program/src/data/future/argument.rs:119"],
    ["program","Argument","ToBits","write_bits_le","100000","","","program/src/data/future/argument.rs:93"],
    ["program","Boolean","Cast","cast","110011","Boolean::new on the input bit","Boolean::new on the input bit","program/src/data/literal/cast/boolean.rs:21"],
    ["program","Boolean","CastLossy","cast_lossy","110011","Boolean::new on the input bit","Boolean::new on the input bit","program/src/data/literal/cast_lossy/boolean.rs:25"],
    ["program","Ciphertext","","decrypt_symmetric","100000","","","program/src/data/ciphertext/decrypt.rs:20"],
    ["program","Ciphertext","","decrypt_with_randomizers","100000","","","program/src/data/ciphertext/decrypt.rs:30"],
    ["program","Ciphertext","Equal","is_equal","100000","","","program/src/data/ciphertext/equal.rs:22"],
    ["program","Ciphertext","Equal","is_not_equal","100000","","","program/src/data/ciphertext/equal.rs:36"],
    ["program","Ciphertext","Inject","new","100000","","","program/src/data/ciphertext/mod.rs:38"],
    ["program","Ciphertext","ToBits","write_bits_be","100000","","","program/src/data/ciphertext/to_bits.rs:29"],
    ["program","Ciphertext","ToBits","write_bits_le","100000","","","program/src/data/ciphertext/to_bits.rs:22"],
    ["program","DynamicFuture","Equal","is_equal","111111","","","program/src/data/dynamic/future/equal.rs:22"],
    ["program","DynamicFuture","Equal","is_not_equal","111111","","","program/src/data/dynamic/future/equal.rs:30"],
    ["program","DynamicFuture","Inject","new","100000","","","program/src/data/dynamic/future/mod.rs:53"],
    ["program","DynamicFuture","ToBits","write_bits_be","100000","","","program/src/data/dynamic/future/to_bits.rs:39"],
    ["program","DynamicFuture","ToBits","write_bits_le","100000","","","program/src/data/dynamic/future/to_bits.rs:23"],
    ["program","DynamicFuture","ToFields","to_fields","100000","","","program/src/data/dynamic/future/to_fields.rs:23"],
    ["program","DynamicRecord","","find","100000","","","program/src/data/dynamic/record/find.rs:20"],
    ["program","DynamicRecord","","from_record","100000","","","program/src/data/dynamic/record/mod.rs:146"],
    ["program","DynamicRecord","","merkleize_data","100000","","","program/src/data/dynamic/record/mod.rs:174"],
    ["program","DynamicRecord","Equal","is_equal","100000","","","program/src/data/dynamic/record/equal.rs:22"],
    ["program","DynamicRecord","Equal","is_not_equal","100000","","","program/src/data/dynamic/record/equal.rs:31"],
    ["program","DynamicRecord","Inject","new","100000","","","program/src/data/dynamic/record/mod.rs:81"],
    ["program","DynamicRecord","ToBits","write_bits_be","100000","","","program/src/data/dynamic/record/to_bits.rs:37"],
    ["program","DynamicRecord","ToBits","write_bits_le","100000","","","program/src/data/dynamic/record/to_bits.rs:22"],
    ["program","DynamicRecord","ToFields","to_fields","100000","","","program/src/data/dynamic/record/to_fields.rs:22"],
    ["program","Entry","","find","100000","","","program/src/data/record/entry/find.rs:20"],
    ["program","Entry","","num_randomizers","100000","","","program/src/data/record/entry/num_randomizers.rs:20"],
    ["program","Entry","","to_fields_with_visibility_as_mode","100000","","","program/src/data/record/entry/to_fields.rs:20"],
    ["program","Entry","","write_bits_le_with_visibility_as_mode","100000","","","program/src/data/record/entry/to_bits.rs:27"],
    ["program","Entry","Equal","is_equal","100000","","","program/src/data/record/entry/equal.rs:22"],
    ["program","Entry","Equal","is_not_equal","100000","","","program/src/data/record/entry/equal.rs:32"],
    ["program","Entry","Inject","new","100000","","","program/src/data/record/entry/mod.rs:41"],
    ["program","Entry","ToBits","write_bits_be","100000","","","program/src/data/record/entry/to_bits.rs:60"],
    ["program","Entry","ToBits","write_bits_le","100000","","","program/src/data/record/entry/to_bits.rs:55"],
    ["program","Entry","ToFields","to_fields","100000","","","program/src/data/record/entry/to_fields.rs:42"],
    ["program","Field","Cast","cast","110011","","","program/src/data/literal/cast/field.rs:26"],
    ["program","Field","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/field.rs:25"],
    ["program","Future","Equal","is_equal","100000","","","program/src/data/future/equal.rs:22"],
    ["program","Future","Equal","is_not_equal","100000","","","program/src/data/future/equal.rs:39"],
    ["program","Future","Inject","new","100000","","","program/src/data/future/mod.rs:43"],
    ["program","Future","ToBits","write_bits_be","100000","","","program/src/data/future/to_bits.rs:54"],
    ["program","Future","ToBits","write_bits_le","100000","","","program/src/data/future/to_bits.rs:24"],
    ["program","Future","ToFields","to_fields","100000","","","program/src/data/future/to_fields.rs:23"],
    ["program","HeaderLeaf","ToBits","write_bits_be","100000","","","program/src/state_path/helpers/header_leaf.rs:72"],
    ["program","HeaderLeaf","ToBits","write_bits_le","100000","","","program/src/state_path/helpers/header_leaf.rs:66"],
    ["program","Identifier","","public","111101","","","program/src/data/identifier/mod.rs:64"],
    ["program","Identifier","Equal","is_equal","111111","","","program/src/data/identifier/equal.rs:22"],
    ["program","Identifier","Equal","is_not_equal","111111","","","program/src/data/identifier/equal.rs:27"],
    ["program","Identifier","FromBits","from_bits_be","100000","","","program/src/data/identifier/from_bits.rs:47"],
    ["program","Identifier","FromBits","from_bits_le","100000","","","program/src/data/identifier/from_bits.rs:22"],
    ["program","Identifier","FromField","from_field","100000","","","program/src/data/identifier/from_field.rs:22"],
    ["program","Identifier","ToBits","write_bits_be","100000","","","program/src/data/identifier/to_bits.rs:27"],
    ["program","Identifier","ToBits","write_bits_le","100000","","","program/src/data/identifier/to_bits.rs:22"],
    ["program","IdentifierLiteral","Cast","cast","110011","IdentifierLiteral::new on the input bytes","IdentifierLiteral::new on the input bytes","program/src/data/literal/cast/identifier.rs:21"],
    ["program","InputID","Inject","new","100000","","","program/src/request/mod.rs:43"],
    ["program","Integer","Cast","cast","110011","Integer::new on the input bits","Integer::new on the input bits","program/src/data/literal/cast/integer.rs:27"],
    ["program","Integer","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/integer.rs:25"],
    ["program","Literal","","from_bits_be","100000","","","program/src/data/literal/from_bits.rs:46"],
    ["program","Literal","","from_bits_le","100000","","","program/src/data/literal/from_bits.rs:20"],
    ["program","Literal","Equal","is_equal","100000","","","program/src/data/literal/equal.rs:22"],
    ["program","Literal","Equal","is_not_equal","100000","","","program/src/data/literal/equal.rs:47"],
    ["program","Literal","Inject","new","111111","Scalar::to_bits_le on the scalar arm's wire","","program/src/data/literal/mod.rs:106"],
    ["program","Literal","ToBits","write_bits_be","100000","","","program/src/data/literal/to_bits.rs:27"],
    ["program","Literal","ToBits","write_bits_le","100000","","","program/src/data/literal/to_bits.rs:22"],
    ["program","Literal","ToFields","to_fields","100000","","","program/src/data/literal/to_fields.rs:22"],
    ["program","OutputID","","dynamic_future","111111","","","program/src/response/mod.rs:157"],
    ["program","OutputID","","dynamic_record","111111","","","program/src/response/mod.rs:147"],
    ["program","OutputID","","external_record","111111","","","program/src/response/mod.rs:127"],
    ["program","OutputID","","future","111111","","","program/src/response/mod.rs:137"],
    ["program","OutputID","","private","111111","","","program/src/response/mod.rs:94"],
    ["program","OutputID","","public","111111","","","program/src/response/mod.rs:84"],
    ["program","OutputID","","record","110101","","","program/src/response/mod.rs:104"],
    ["program","Owner","","decrypt","100000","","","program/src/data/record/helpers/owner.rs:145"],
    ["program","Owner","","encrypt","100000","","","program/src/data/record/helpers/owner.rs:118"],
    ["program","Owner","","to_entry","100000","","","program/src/data/record/helpers/owner.rs:86"],
    ["program","Owner","Equal","is_equal","100000","","","program/src/data/record/helpers/owner.rs:98"],
    ["program","Owner","Equal","is_not_equal","100000","","","program/src/data/record/helpers/owner.rs:107"],
    ["program","Owner","Inject","new","100000","","","program/src/data/record/helpers/owner.rs:33"],
    ["program","Plaintext","","encrypt","100000","","","program/src/data/plaintext/encrypt.rs:20"],
    ["program","Plaintext","","encrypt_symmetric","100000","","","program/src/data/plaintext/encrypt.rs:28"],
    ["program","Plaintext","","encrypt_with_randomizers","100000","","","program/src/data/plaintext/encrypt.rs:38"],
    ["program","Plaintext","","find","100000","","","program/src/data/plaintext/find.rs:20"],
    ["program","Plaintext","","from_bit_array","100000","","","program/src/data/plaintext/mod.rs:50"],
    ["program","Plaintext","","from_bits_be_internal","100000","","","program/src/data/plaintext/from_bits.rs:123"],
    ["program","Plaintext","","from_bits_le_internal","100000","","","program/src/data/plaintext/from_bits.rs:34"],
    ["program","Plaintext","","num_randomizers","100000","","","program/src/data/plaintext/num_randomizers.rs:20"],
    ["program","Plaintext","Equal","is_equal","100000","","","program/src/data/plaintext/equal.rs:22"],
    ["program","Plaintext","Equal","is_not_equal","100000","","","program/src/data/plaintext/equal.rs:52"],
    ["program","Plaintext","From","from","100000","","","program/src/data/plaintext/from_fields.rs:20"],
    ["program","Plaintext","FromBits","from_bits_be","100000","","","program/src/data/plaintext/from_bits.rs:27"],
    ["program","Plaintext","FromBits","from_bits_le","100000","","","program/src/data/plaintext/from_bits.rs:22"],
    ["program","Plaintext","FromFields","from_fields","100000","","","program/src/data/plaintext/from_fields.rs:36"],
    ["program","Plaintext","Inject","new","100000","","","program/src/data/plaintext/mod.rs:77"],
    ["program","Plaintext","ToBits","write_bits_be","100000","","","program/src/data/plaintext/to_bits.rs:80"],
    ["program","Plaintext","ToBits","write_bits_le","100000","","","program/src/data/plaintext/to_bits.rs:24"],
    ["program","Plaintext","ToBitsRaw","write_bits_raw_be","100000","","","program/src/data/plaintext/to_bits_raw.rs:42"],
    ["program","Plaintext","ToBitsRaw","write_bits_raw_le","100000","","","program/src/data/plaintext/to_bits_raw.rs:20"],
    ["program","Plaintext","ToFields","to_fields","100000","","","program/src/data/plaintext/to_fields.rs:22"],
    ["program","Plaintext","ToFieldsRaw","to_fields_raw","100000","","","program/src/data/plaintext/to_fields_raw.rs:20"],
    ["program","Plaintext","Visibility","size_in_fields","100000","","","program/src/data/plaintext/size_in_fields.rs:20"],
    ["program","ProgramID","","public","111101","","","program/src/id/mod.rs:45"],
    ["program","ProgramID","","to_address","110001","","","program/src/id/to_address.rs:20"],
    ["program","ProgramID","Equal","is_equal","111111","","","program/src/id/mod.rs:85"],
    ["program","ProgramID","Equal","is_not_equal","111111","","","program/src/id/mod.rs:90"],
    ["program","ProgramID","ToBits","write_bits_be","100000","","","program/src/id/to_bits.rs:27"],
    ["program","ProgramID","ToBits","write_bits_le","100000","","","program/src/id/to_bits.rs:22"],
    ["program","ProgramID","ToFields","to_fields","111101","","","program/src/id/to_fields.rs:22"],
    ["program","Record","","decrypt","100000","","","program/src/data/record/decrypt.rs:20"],
    ["program","Record","","decrypt_symmetric_unchecked","100000","","","program/src/data/record/decrypt.rs:34"],
    ["program","Record","","decrypt_with_randomizers","100000","","","program/src/data/record/decrypt.rs:44"],
    ["program","Record","","encrypt","100000","","","program/src/data/record/encrypt.rs:20"],
    ["program","Record","","encrypt_symmetric","100000","","","program/src/data/record/encrypt.rs:27"],
    ["program","Record","","encrypt_symmetric_unchecked","100000","","","program/src/data/record/encrypt.rs:42"],
    ["program","Record","","encrypt_with_randomizers","100000","","","program/src/data/record/encrypt.rs:52"],
    ["program","Record","","find","100000","","","program/src/data/record/find.rs:20"],
    ["program","Record","","is_hiding","111111","Integer::new on the version","","program/src/data/record/mod.rs:155"],
    ["program","Record","","num_randomizers","100000","","","program/src/data/record/num_randomizers.rs:20"],
    ["program","Record","","serial_number","100000","","","program/src/data/record/serial_number.rs:20"],
    ["program","Record","","serial_number_from_gamma","100000","","","program/src/data/record/serial_number.rs:30"],
    ["program","Record","","to_commitment","100000","","","program/src/data/record/to_commitment.rs:20"],
    ["program","Record","Equal","is_equal","100000","","","program/src/data/record/equal.rs:24"],
    ["program","Record","Equal","is_not_equal","100000","","","program/src/data/record/equal.rs:45"],
    ["program","Record","Inject","new","100000","","","program/src/data/record/mod.rs:59"],
    ["program","Record","ToBits","write_bits_be","100000","","","program/src/data/record/to_bits.rs:63"],
    ["program","Record","ToBits","write_bits_le","100000","","","program/src/data/record/to_bits.rs:22"],
    ["program","Record","ToFields","to_fields","100000","","","program/src/data/record/to_fields.rs:22"],
    ["program","Request","","check_input_ids","100000","","","program/src/request/verify.rs:124"],
    ["program","Request","","to_tpk","100000","","","program/src/request/to_tpk.rs:20"],
    ["program","Request","","verify","100000","","","program/src/request/verify.rs:25"],
    ["program","Request","Inject","new","100000","","","program/src/request/mod.rs:163"],
    ["program","Response","","from_outputs","100000","","","program/src/response/from_outputs.rs:20"],
    ["program","Response","","process_outputs_from_callback","100000","","","program/src/response/process_outputs_from_callback.rs:20"],
    ["program","Scalar","Cast","cast","110011","Scalar::new on the input scalar","Scalar::new on the input scalar","program/src/data/literal/cast/scalar.rs:27"],
    ["program","Scalar","CastLossy","cast_lossy","100000","","","program/src/data/literal/cast_lossy/scalar.rs:25"],
    ["program","StatePath","","verify","100000","","","program/src/state_path/verify.rs:55"],
    ["program","TransactionLeaf","ToBits","write_bits_be","100000","","","program/src/state_path/helpers/transaction_leaf.rs:84"],
    ["program","TransactionLeaf","ToBits","write_bits_le","100000","","","program/src/state_path/helpers/transaction_leaf.rs:77"],
    ["program","TransitionLeaf","ToBits","write_bits_be","100000","","","program/src/state_path/helpers/transition_leaf.rs:101"],
    ["program","TransitionLeaf","ToBits","write_bits_le","100000","","","program/src/state_path/helpers/transition_leaf.rs:93"],
    ["program","Value","","find","100000","","","program/src/data/value/find.rs:20"],
    ["program","Value","Equal","is_equal","100000","","","program/src/data/value/equal.rs:22"],
    ["program","Value","Equal","is_not_equal","100000","","","program/src/data/value/equal.rs:38"],
    ["program","Value","Inject","new","100000","","","program/src/data/value/mod.rs:45"],
    ["program","Value","ToBits","write_bits_be","100000","","","program/src/data/value/to_bits.rs:35"],
    ["program","Value","ToBits","write_bits_le","100000","","","program/src/data/value/to_bits.rs:23"],
    ["program","Value","ToBitsRaw","write_bits_raw_be","100000","","","program/src/data/value/to_bits_raw.rs:34"],
    ["program","Value","ToBitsRaw","write_bits_raw_le","100000","","","program/src/data/value/to_bits_raw.rs:21"],
    ["program","Value","ToFields","to_fields","100000","","","program/src/data/value/to_fields.rs:23"],
    ["program","Value","ToFieldsRaw","to_fields_raw","100000","","","program/src/data/value/to_fields_raw.rs:21"],
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
    ["types/field","Field","","square_roots_flagged_nondeterministic","110000","","","types/field/src/square_root.rs:85"],
    ["types/field","Field","","to_non_unique_bits_le","110101","","","types/field/src/helpers/to_bits.rs:68"],
    ["types/field","Field","Compare","is_greater_than","111111","","","types/field/src/compare.rs:79"],
    ["types/field","Field","Compare","is_greater_than_or_equal","111111","","","types/field/src/compare.rs:89"],
    ["types/field","Field","Compare","is_less_than","111111","","","types/field/src/compare.rs:22"],
    ["types/field","Field","Compare","is_less_than_or_equal","111111","","","types/field/src/compare.rs:84"],
    ["types/field","Field","Div","div","111111","","","types/field/src/div.rs:21"],
    ["types/field","Field","DivAssign","div_assign","111111","","","types/field/src/div.rs:53"],
    ["types/field","Field","DivUnchecked","div_unchecked","111101","","","types/field/src/div_unchecked.rs:24"],
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
    ["types/field","Field","ToLowerBits","to_lower_bits_be","111101","","","types/field/src/helpers/to_lower_bits.rs:56"],
    ["types/field","Field","ToLowerBits","to_lower_bits_le","111101","","","types/field/src/helpers/to_lower_bits.rs:25"],
    ["types/field","Field","ToUpperBits","to_upper_bits_be","111101","","","types/field/src/helpers/to_upper_bits.rs:35"],
    ["types/field","Field","ToUpperBits","to_upper_bits_le","111101","","","types/field/src/helpers/to_upper_bits.rs:25"],
    ["types/field","Field","Zero","is_zero","111111","","","types/field/src/helpers/zero.rs:25"],
    ["types/group","Group","","enforce_double","110011","Group::new on self","","types/group/src/double.rs:67"],
    ["types/group","Group","","enforce_in_group","110011","","","types/group/src/lib.rs:101"],
    ["types/group","Group","","enforce_on_curve","111111","","","types/group/src/lib.rs:83"],
    ["types/group","Group","","from_x_coordinate","110011","","","types/group/src/helpers/from_x_coordinate.rs:21"],
    ["types/group","Group","","from_x_coordinate_flagged","110000","","","types/group/src/helpers/from_x_coordinate.rs:35"],
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
    ["types/integers","Integer","","mul_with_flags","100000","","","types/integers/src/pow_checked.rs:103"],
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
    [0,100],
    [1,100],
    [2,348],[2,430],
    [3,2],
    [4,114],
    [7,352],
    [8,357],[8,436],
    [9,358],
    [10,359],
    [12,0],
    [13,24],
    [14,1],[14,100],[14,430],
    [16,15],
    [17,5],
    [18,6],
    [19,7],
    [20,8],[20,436],
    [21,9],[21,437],
    [22,10],[22,438],
    [25,100],
    [26,27],
    [27,28],
    [28,29],
    [29,314],[29,347],
    [31,322],[31,339],
    [32,403],
    [33,403],
    [34,36],
    [35,73],
    [37,38],
    [38,39],
    [44,41],[44,42],
    [45,46],
    [48,31],[48,47],
    [49,423],
    [54,53],
    [55,300],
    [56,304],
    [60,329],
    [62,352],
    [63,62],
    [71,322],
    [79,7],[79,19],[79,30],[79,50],[79,55],[79,58],[79,61],[79,64],[79,122],[79,131],[79,136],[79,145],[79,155],[79,163],[79,178],[79,185],[79,201],[79,216],[79,246],[79,253],[79,266],[79,283],[79,300],[79,352],[79,392],[79,446],
    [101,47],
    [102,47],
    [103,47],
    [110,48],
    [111,48],
    [112,48],
    [113,49],
    [114,49],
    [115,49],
    [119,73],
    [125,126],
    [126,284],[126,320],[126,357],[126,419],[126,436],
    [127,103],
    [134,315],
    [135,134],
    [137,330],
    [138,331],
    [139,73],
    [140,212],
    [141,142],
    [143,277],[143,315],[143,348],
    [144,143],
    [146,285],[146,330],[146,358],
    [147,286],[147,331],[147,359],
    [148,73],
    [150,223],[150,294],
    [151,152],
    [152,300],
    [155,131],[155,216],
    [157,152],
    [158,151],
    [159,282],[159,325],[159,336],[159,340],[159,391],[159,434],[159,451],
    [160,31],[160,73],[160,329],[160,341],[160,361],[160,423],
    [161,170],[161,226],
    [162,171],[162,227],
    [164,72],
    [166,73],
    [167,330],
    [168,331],
    [170,315],
    [171,316],
    [172,173],
    [173,319],
    [174,73],
    [175,176],
    [176,331],
    [177,454],
    [178,352],
    [179,73],[179,288],[179,399],[179,420],[179,422],
    [180,73],[180,365],[180,390],[180,420],
    [181,17],[181,318],[181,350],[181,432],[181,449],
    [182,18],[182,319],[182,351],[182,433],[182,450],
    [185,300],
    [198,212],
    [201,131],[201,283],
    [202,203],
    [203,103],
    [205,294],
    [206,212],
    [209,223],
    [212,215],
    [213,207],
    [214,208],
    [215,73],
    [217,72],
    [218,73],
    [219,72],
    [220,73],[220,75],
    [221,73],
    [222,75],
    [223,73],
    [224,169],
    [225,111],
    [226,170],
    [227,171],
    [231,232],
    [232,103],
    [233,196],
    [234,235],
    [235,100],
    [236,103],
    [237,197],[237,204],
    [241,110],
    [242,73],[242,90],[242,344],
    [244,199],[244,348],
    [245,200],[245,349],
    [247,72],[247,239],[247,358],
    [248,73],[248,239],[248,359],
    [249,73],
    [250,110],[250,243],
    [251,100],
    [252,277],
    [253,266],
    [254,189],[254,190],[254,191],[254,192],[254,193],[254,194],[254,195],[254,243],
    [255,189],[255,190],[255,191],[255,192],[255,193],[255,194],[255,243],[255,266],
    [256,73],[256,435],[256,439],
    [257,73],
    [258,116],[258,304],[258,331],
    [259,330],
    [260,331],
    [261,330],
    [262,331],
    [266,136],[266,145],[266,216],[266,246],
    [272,222],
    [273,275],
    [274,275],
    [276,274],
    [277,348],
    [278,349],
    [279,282],
    [280,350],
    [281,351],
    [282,340],
    [283,352],
    [284,357],
    [285,358],
    [286,359],
    [289,290],
    [291,292],[291,294],[291,296],
    [292,293],
    [294,295],
    [296,297],
    [298,299],
    [299,296],
    [301,292],
    [302,292],
    [303,292],[303,294],[303,296],
    [304,292],[304,294],
    [305,72],
    [306,328],[306,329],[306,398],
    [307,323],[307,347],
    [308,310],
    [309,310],
    [310,304],
    [311,309],
    [312,313],
    [313,322],[313,323],[313,324],
    [314,294],[314,322],
    [315,316],
    [316,300],
    [317,287],
    [318,319],
    [319,288],[319,289],[319,323],[319,347],
    [320,287],[320,317],
    [321,322],
    [323,324],
    [324,294],
    [325,315],
    [326,323],[326,324],[326,329],
    [327,323],
    [329,323],
    [330,331],
    [331,289],[331,307],
    [332,333],
    [333,323],[333,347],
    [334,289],[334,323],[334,347],
    [335,334],
    [336,315],
    [337,345],[337,347],[337,355],
    [338,337],[338,339],[338,347],
    [339,355],
    [340,342],
    [341,306],[341,329],[341,343],[341,355],
    [342,338],
    [344,347],
    [346,345],
    [347,345],[347,355],
    [348,292],[348,315],
    [349,348],
    [350,318],
    [351,319],
    [352,338],
    [353,354],
    [354,72],[354,345],[354,347],[354,357],
    [355,345],
    [356,345],[356,355],
    [357,329],
    [358,330],
    [359,331],
    [360,292],[360,315],
    [361,73],
    [362,333],
    [363,288],
    [364,362],
    [365,433],
    [366,371],[366,396],
    [367,417],
    [368,418],[368,419],
    [369,370],
    [370,371],
    [371,292],[371,333],[371,373],
    [372,333],
    [373,292],[373,293],[373,374],
    [374,292],[374,293],
    [375,294],[375,295],[375,376],
    [376,294],[376,295],
    [377,296],[377,297],[377,378],
    [378,296],[378,297],
    [379,381],
    [380,381],
    [381,292],[381,333],[381,373],
    [382,380],
    [383,384],
    [384,385],
    [385,292],[385,368],[385,373],[385,386],[385,387],[385,398],[385,418],[385,419],
    [386,366],
    [387,292],[387,373],
    [388,387],
    [389,390],
    [390,288],
    [391,333],
    [392,292],[392,300],[392,373],
    [393,406],
    [394,395],
    [395,396],
    [396,292],[396,294],[396,363],[396,373],[396,375],
    [397,333],
    [398,371],
    [399,387],
    [400,401],
    [401,292],[401,294],[401,368],[401,373],[401,375],[401,392],[401,396],[401,419],
    [402,397],[402,419],
    [403,404],
    [404,405],
    [405,292],[405,368],[405,373],[405,387],[405,398],[405,406],[405,418],[405,419],
    [406,366],
    [407,408],
    [408,409],
    [409,288],[409,329],[409,333],[409,396],[409,401],
    [410,329],[410,333],[410,397],
    [411,412],
    [412,413],
    [413,288],[413,392],
    [414,329],[414,333],[414,366],[414,368],[414,372],[414,386],[414,418],[414,419],
    [415,416],
    [416,417],
    [417,292],[417,333],[417,373],
    [418,333],
    [419,304],
    [420,319],
    [421,420],
    [422,387],
    [423,73],[423,433],
    [424,425],
    [425,333],
    [426,428],
    [427,428],
    [428,300],[428,347],
    [429,427],
    [430,315],
    [431,430],
    [432,433],
    [433,288],[433,289],[433,347],[433,424],[433,425],
    [434,73],[434,433],
    [435,430],
    [436,329],
    [437,438],
    [438,289],[438,333],
    [439,430],
    [440,292],[440,294],
    [441,292],[441,294],
    [442,292],[442,296],
    [443,292],[443,446],
    [446,292],
    [449,450],
    [450,288],
    [451,73],[451,450],
    [452,453],
    [454,319],
    [455,454],
  ],
  d: [
    ["Inject::new",[7,19,30,50,55,58,64,79,122,131,136,145,155,163,178,185,201,216,246,253,266,283,300,352,392]],
    ["Ternary::ternary",[8,20,56,284,304,329,357,419,436]],
    ["add",[345,369,424]],
    ["bitand",[292,373]],
    ["bitor",[294,375]],
    ["bitxor",[296,377]],
    ["cast",[125,159,177,179,256]],
    ["cast_lossy",[126,160,180,257]],
    ["commit",[26,37]],
    ["commit_uncompressed",[27,38]],
    ["encrypt_symmetric",[203,235]],
    ["find",[140,149,205,238,263]],
    ["hash_children",[52,59]],
    ["hash_uncompressed",[28,29,39]],
    ["is_equal",[2,15,53,120,129,134,143,153,161,170,183,199,210,226,244,264,277,298,315,348,387,430,447]],
    ["is_less_than",[275,310,381,428]],
    ["is_less_than_or_equal",[276,311,382,429]],
    ["is_not_equal",[3,16,54,121,130,135,144,154,162,171,184,200,211,227,245,265,278,299,316,349,388,431,448]],
    ["is_one",[325,399,435]],
    ["is_zero",[336,360,422,439]],
    ["mul",[323,353,394]],
    ["num_randomizers",[150,209]],
    ["op &=",[292,293]],
    ["op *",[323,353,394]],
    ["op +",[345,369,424]],
    ["op +=",[345,346,369,370,424,425]],
    ["op -",[355,415]],
    ["op |=",[294,295]],
    ["pow",[326,400]],
    ["t0::new",[7,19,30,50,55,58,61,79,122,131,136,145,155,163,178,185,201,216,246,253,266,283,300,352,392,446]],
    ["to_address",[1,25,225]],
    ["to_field",[420,454]],
    ["to_fields",[11,23,139,148,158,166,188,221,230,249,271,421,455]],
    ["ty::new",[7,19,30,50,55,58,61,79,122,131,136,145,155,163,178,185,201,216,246,253,266,283,300,352,392,446]],
    ["verify",[14,57,60,252,258]],
    ["write_bits_be",[9,21,65,80,84,123,132,137,146,156,164,167,175,186,217,228,247,259,261,267,285,330,358,437,452]],
    ["write_bits_le",[10,22,66,81,85,124,133,138,147,157,165,168,176,187,218,229,248,260,262,268,286,331,359,438,453]],
    ["write_bits_raw_be",[67,82,86,219,269]],
    ["write_bits_raw_le",[68,83,87,220,270]],
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
    [64,29],[64,33],
    [65,35],
    [66,36],
    [67,37],
    [68,38],
    [72,35],
    [73,36],
    [74,37],
    [75,38],
    [80,35],
    [81,36],
    [82,37],
    [83,38],
    [84,35],
    [85,36],
    [86,37],
    [87,38],
    [88,8],
    [89,8],
    [90,8],
    [91,8],
    [92,8],
    [93,8],
    [94,9],
    [95,9],
    [96,9],
    [97,9],
    [98,9],
    [99,9],
    [100,24],
    [104,13],
    [105,13],
    [106,13],
    [107,13],
    [108,13],
    [109,13],
    [116,34],
    [117,34],
    [120,14],
    [121,17],
    [122,0],
    [123,35],
    [124,36],
    [125,6],
    [128,26],
    [129,22],
    [130,17],[130,27],
    [131,0],
    [132,23],[132,26],[132,35],
    [133,23],[133,26],[133,36],
    [136,0],
    [142,31],[142,32],
    [143,14],
    [145,0],
    [146,35],
    [147,36],
    [149,11],
    [153,14],
    [154,17],
    [156,35],
    [157,36],
    [159,4],
    [161,14],[161,22],
    [162,17],[162,27],
    [163,0],
    [164,35],
    [165,36],
    [167,35],
    [168,36],
    [169,31],
    [177,6],
    [179,4],[179,6],
    [180,7],
    [183,14],
    [184,17],
    [186,35],
    [187,36],
    [188,31],[188,32],
    [195,14],
    [196,26],
    [197,24],
    [199,14],
    [200,17],
    [202,23],
    [204,24],
    [207,24],[207,25],
    [208,24],[208,25],
    [210,14],[210,22],
    [211,17],[211,27],
    [216,0],
    [217,35],
    [218,36],
    [228,35],
    [229,36],
    [230,31],
    [231,23],[231,30],
    [233,24],[233,25],
    [237,24],[237,25],
    [238,11],
    [239,19],
    [240,21],
    [243,1],
    [244,14],
    [245,17],
    [246,0],
    [247,35],
    [248,36],
    [250,10],[250,14],[250,24],
    [251,24],
    [252,1],[252,14],[252,30],
    [254,10],[254,24],
    [255,10],[255,24],
    [256,4],[256,6],
    [257,7],
    [258,14],
    [259,35],
    [260,36],
    [261,35],
    [262,36],
    [263,11],
    [264,14],
    [265,17],
    [267,35],
    [268,36],
    [269,35],[269,37],
    [270,36],
    [271,32],
    [272,32],
    [275,15],
    [287,31],
    [290,3],[290,4],
    [306,3],[306,18],
    [310,3],[310,4],[310,5],
    [313,19],
    [314,19],
    [328,16],
    [341,3],[341,4],
    [343,19],[343,20],
    [345,19],
    [347,19],
    [364,17],
    [366,15],
    [371,14],[371,17],
    [381,14],
    [385,14],
    [386,14],
    [387,14],
    [396,14],
    [401,14],
    [409,14],
    [410,28],
    [414,2],[414,14],[414,28],
    [417,14],[417,17],
    [425,1],[425,15],
    [444,36],
    [446,14],
    [447,14],
    [448,17],
    [453,36],
    [454,36],
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
