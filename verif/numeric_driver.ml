(* Test adapter only. The arithmetic under test is entirely extracted Rocq. *)
open Spada_numeric
open Spada
open SpatialSemantics
let rec positive n =
  if n = 1L then XH else
  let tail = positive (Int64.shift_right_logical n 1) in
  if Int64.logand n 1L = 0L then XO tail else XI tail
let z_of_hex s = let n = Int64.of_string ("0x" ^ s) in if n = 0L then Z0 else Zpos (positive n)
let rec unsigned = function
  | XH -> 1L | XO p -> Int64.shift_left (unsigned p) 1
  | XI p -> Int64.logor (Int64.shift_left (unsigned p) 1) 1L
let word = function Z0 -> 0L | Zpos p -> unsigned p | Zneg p -> Int64.neg (unsigned p)
let scalar = function "f16" -> F16 | "f32" -> F32 | "f64" -> F64 | "i32" -> I32 | "u32" -> U32 | _ -> failwith "type"
let operation = function "add" -> Plus | "sub" -> Minus | "mul" -> Times | "div" -> Divide | _ -> failwith "op"
let atom t v = {atom_type = scalar t; atom_bits = z_of_hex v}
let () =
  try while true do
    let fields = String.split_on_char ' ' (read_line ()) in
    let result = match fields with
      | [t; "fma"; a; b; c] -> ReferenceArithmetic.fma_reference (atom t a) (atom t b) (atom t c)
      | [t; op; a; b] -> ReferenceArithmetic.binary_reference (operation op) (atom t a) (atom t b)
      | _ -> failwith "input" in
    (match result with None -> print_endline "none" | Some v -> Printf.printf "%Lx\n%!" (word v.atom_bits))
  done with End_of_file -> ()
