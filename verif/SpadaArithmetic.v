From Stdlib Require Import ZArith Bool List.
From SpatialCSL Require Import SpadaIR SpadaSemantics.
Import Spada SpatialSemantics.
Open Scope Z_scope.

Module ReferenceArithmetic.
Definition bits (t : scalar) : Z := match t with
 | I8 | U8 => 8 | I16 | U16 | F16 => 16 | I32 | U32 | F32 => 32
 | F64 => 64 | Bool => 1 end.
Definition signed (t : scalar) := match t with I8 | I16 | I32 => true | _ => false end.
Definition floating (t : scalar) := match t with F16 | F32 | F64 => true | _ => false end.
Definition mask (n : Z) := 2^n-1.
Definition normalize t z := z mod (2 ^ bits t).
Definition integer_value (a : atom) :=
 let n := normalize (atom_type a) (atom_bits a) in
 if (signed (atom_type a) && Z.testbit n (bits (atom_type a)-1))%bool
 then n-2^bits (atom_type a) else n.
Definition exponent_bits t := match t with F16 => 5 | F32 => 8 | _ => 11 end.
Definition fraction_bits t := match t with F16 => 10 | F32 => 23 | _ => 52 end.
Definition bias t := 2^(exponent_bits t-1)-1.
Inductive fp := NaN (payload : Z) | Infinity (negative : bool)
 | Finite (negative : bool) (mantissa exponent : Z).
Definition sign_bit (t : scalar) (s : bool) := if s then 2^(bits t-1) else 0.
Definition decode t raw :=
 let raw := normalize t raw in
 let s := Z.testbit raw (bits t-1) in
 let f := Z.land raw (mask (fraction_bits t)) in
 let e := Z.land (Z.shiftr raw (fraction_bits t)) (mask (exponent_bits t)) in
 if Z.eqb e (mask (exponent_bits t)) then
   if Z.eqb f 0 then Infinity s else NaN raw
 else Finite s (if Z.eqb e 0 then f else 2^fraction_bits t+f)
   ((if Z.eqb e 0 then 1 else e)-bias t-fraction_bits t).
Definition nan_bits t := (mask (exponent_bits t) * 2^fraction_bits t + 2^(fraction_bits t-1)).
Definition inf_bits t s := sign_bit t s + mask (exponent_bits t)*2^fraction_bits t.
Definition signed_mantissa (s : bool) m := if s then -m else m.
Definition round_div n d :=
 let q := n / d in let r := n mod d in
 if (Z.ltb d (2*r) || (Z.eqb (2*r) d && Z.odd q))%bool then q+1 else q.
Definition ratio_log2 n d :=
 let k := Z.log2 n-Z.log2 d in
 if (if Z.leb 0 k then Z.ltb n (Z.shiftl d k)
     else Z.ltb (Z.shiftl n (-k)) d) then k-1 else k.
(** Exact round-to-nearest, ties-to-even. Gradual underflow and overflow to
    infinity are explicit; no OCaml machine integer or host float is used. *)
Definition round_ratio t s n d e :=
 if Z.eqb n 0 then sign_bit t s else
 let f := fraction_bits t in
 let unit := Z.max (1-bias t-f) (ratio_log2 n d+e-f) in
 let shift := e-unit in
 let q := if Z.leb 0 shift then round_div (Z.shiftl n shift) d
          else round_div n (Z.shiftl d (-shift)) in
 let '(q,unit) := if Z.leb (2^(f+1)) q then (q/2,unit+1) else (q,unit) in
 let ef := if Z.ltb q (2^f) then 0 else unit+f+bias t in
 if Z.leb (mask (exponent_bits t)) ef then inf_bits t s else
 sign_bit t s + ef*2^f + (if Z.eqb ef 0 then q else q-2^f).
Definition encode t f := match f with
 | NaN _ => nan_bits t | Infinity s => inf_bits t s
 | Finite s m e => round_ratio t s m 1 e end.
Definition fp_neg f := match f with
 | NaN p => NaN p | Infinity s => Infinity (negb s)
 | Finite s m e => Finite (negb s) m e end.
Definition fp_add a b := match a,b with
 | NaN p,_ | _,NaN p => NaN p
 | Infinity a, Infinity b => if Bool.eqb a b then Infinity a else NaN 0
 | Infinity s,_ | _,Infinity s => Infinity s
 | Finite sa ma ea,Finite sb mb eb =>
   let e := Z.min ea eb in
   let z := signed_mantissa sa (Z.shiftl ma (ea-e)) + signed_mantissa sb (Z.shiftl mb (eb-e)) in
   Finite (if Z.eqb z 0 then (sa && sb)%bool else Z.ltb z 0) (Z.abs z) e end.
Definition fp_mul a b := match a,b with
 | NaN p,_ | _,NaN p => NaN p
 | Infinity sa,Infinity sb => Infinity (xorb sa sb)
 | Infinity sa,Finite sb m _ | Finite sb m _,Infinity sa =>
   if Z.eqb m 0 then NaN 0 else Infinity (xorb sa sb)
 | Finite sa ma ea,Finite sb mb eb => Finite (xorb sa sb) (ma*mb) (ea+eb) end.
Definition fp_div_bits t a b := match a,b with
 | NaN _,_ | _,NaN _ | Infinity _, Infinity _ => nan_bits t
 | Infinity sa,Finite sb _ _ => inf_bits t (xorb sa sb)
 | Finite sa _ _,Infinity sb => sign_bit t (xorb sa sb)
 | Finite sa ma ea,Finite sb mb eb =>
   if Z.eqb mb 0 then if Z.eqb ma 0 then nan_bits t else inf_bits t (xorb sa sb)
   else round_ratio t (xorb sa sb) ma mb (ea-eb) end.
Definition fp_compare a b : option comparison := match a,b with
 | NaN _,_ | _,NaN _ => None
 | Infinity sa,Infinity sb => Some (if Bool.eqb sa sb then Eq else if sa then Lt else Gt)
 | Infinity sa,_ => Some (if sa then Lt else Gt)
 | _,Infinity sb => Some (if sb then Gt else Lt)
 | Finite sa ma ea,Finite sb mb eb =>
   let e := Z.min ea eb in
   Some (Z.compare (signed_mantissa sa (Z.shiftl ma (ea-e)))
                   (signed_mantissa sb (Z.shiftl mb (eb-e)))) end.
Definition numeric_truth a :=
 if floating (atom_type a) then match decode (atom_type a) (atom_bits a) with
 | Finite _ m _ => negb (Z.eqb m 0) | _ => true end
 else negb (Z.eqb (integer_value a) 0).
Definition bool_atom (b : bool) := Atom Bool (if b then 1 else 0).
Definition cast t a :=
 if floating t then
   let f := if floating (atom_type a) then decode (atom_type a) (atom_bits a)
            else let z := integer_value a in Finite (Z.ltb z 0) (Z.abs z) 0 in
   Some (Atom t (encode t f))
 else if floating (atom_type a) then
   match decode (atom_type a) (atom_bits a) with
   | Finite s m e => let n := if Z.leb 0 e then Z.shiftl m e else Z.shiftr m (-e) in
     Some (Atom t (normalize t (signed_mantissa s n)))
   | _ => None end
 else Some (Atom t (if match t with Bool => true | _ => false end
 then if numeric_truth a then 1 else 0 else normalize t (integer_value a))).
Definition promote (a b : scalar) :=
 if floating a then if floating b then if Z.leb (bits a) (bits b) then b else a else a
 else if floating b then b
 else if Z.ltb (bits a) (bits b) then b
 else if (Z.eqb (bits a) (bits b) && signed a)%bool then b else a.
Definition literal_reference t v := match v with
 | BooleanValue b => cast t (bool_atom b)
 | Integer z => if floating t then Some (Atom t (encode t (Finite (Z.ltb z 0) (Z.abs z) 0)))
   else Some (Atom t (normalize t z))
 | FloatBits z => if floating t then Some (Atom t (normalize t z)) else None end.
Definition unary_reference op a := match op with
 | Positive => Some a
 | LogicalNot => Some (bool_atom (negb (numeric_truth a)))
 | BitNot => if floating (atom_type a) then None else
   Some (Atom (atom_type a) (normalize (atom_type a) (Z.lnot (integer_value a))))
 | Negative => if floating (atom_type a) then
     Some (Atom (atom_type a) (encode (atom_type a) (fp_neg (decode (atom_type a) (atom_bits a)))))
   else Some (Atom (atom_type a) (normalize (atom_type a) (-integer_value a))) end.
Definition comparison_result op cmp :=
 match op with
 | Equal => Some (bool_atom (match cmp with Some Eq => true | _ => false end))
 | NotEqual => Some (bool_atom (match cmp with Some Eq => false | _ => true end))
 | Less => Some (bool_atom (match cmp with Some Lt => true | _ => false end))
 | LessEqual => Some (bool_atom (match cmp with Some Lt | Some Eq => true | _ => false end))
 | Greater => Some (bool_atom (match cmp with Some Gt => true | _ => false end))
 | GreaterEqual => Some (bool_atom (match cmp with Some Gt | Some Eq => true | _ => false end))
 | _ => None end.
Definition binary_reference op a b :=
 match op with
 | LogicalAnd => Some (bool_atom (andb (numeric_truth a) (numeric_truth b)))
 | LogicalOr => Some (bool_atom (orb (numeric_truth a) (numeric_truth b)))
 | _ =>
 let t := promote (atom_type a) (atom_type b) in
 obind (cast t a) (fun a => obind (cast t b) (fun b =>
 if floating t then
   let x := decode t (atom_bits a) in let y := decode t (atom_bits b) in
   match op with
   | Plus => Some (Atom t (encode t (fp_add x y)))
   | Minus => Some (Atom t (encode t (fp_add x (fp_neg y))))
   | Times => Some (Atom t (encode t (fp_mul x y)))
   | Divide => Some (Atom t (fp_div_bits t x y))
   | _ => comparison_result op (fp_compare x y) end
 else let x := integer_value a in let y := integer_value b in
   let wrap z := Some (Atom t (normalize t z)) in
   match op with
   | Plus => wrap (x+y) | Minus => wrap (x-y) | Times => wrap (x*y)
   | BitAnd => wrap (Z.land x y) | BitOr => wrap (Z.lor x y) | BitXor => wrap (Z.lxor x y)
   | Power => if Z.leb 0 y then wrap (x^y) else None
   | Divide => if Z.eqb y 0 then None else wrap (Z.quot x y)
   | Modulo => if Z.eqb y 0 then None else wrap (Z.rem x y)
   | ShiftLeft => if (Z.leb 0 y && Z.ltb y (bits t))%bool then wrap (Z.shiftl x y) else None
   | ShiftRight => if (Z.leb 0 y && Z.ltb y (bits t))%bool then wrap (Z.shiftr x y) else None
   | _ => comparison_result op (Some (Z.compare x y)) end)) end.
Definition fma_reference a b c :=
 let t := promote (atom_type a) (promote (atom_type b) (atom_type c)) in
 obind (cast t a) (fun a => obind (cast t b) (fun b => obind (cast t c) (fun c =>
 if floating t then Some (Atom t (encode t (fp_add (decode t (atom_bits a))
   (fp_mul (decode t (atom_bits b)) (decode t (atom_bits c))))))
 else Some (Atom t (normalize t (integer_value a + integer_value b * integer_value c)))))).
Definition reference : arithmetic := Arithmetic literal_reference unary_reference
 binary_reference fma_reference cast numeric_truth
 (fun a => if floating (atom_type a) then None else Some (integer_value a)).

Example f32_one_plus_one : binary_reference Plus (Atom F32 1065353216) (Atom F32 1065353216) =
 Some (Atom F32 1073741824).
Proof. vm_compute; reflexivity. Qed.
Example f16_smallest_subnormal_add : binary_reference Plus (Atom F16 1) (Atom F16 1) = Some (Atom F16 2).
Proof. vm_compute; reflexivity. Qed.
Example f64_negative_zero_times_one : binary_reference Times
 (Atom F64 9223372036854775808) (Atom F64 4607182418800017408) = Some (Atom F64 9223372036854775808).
Proof. vm_compute; reflexivity. Qed.
Example f32_ties_to_even : binary_reference Plus (Atom F32 1065353216)
 (Atom F32 864026624) = Some (Atom F32 1065353216).
Proof. vm_compute; reflexivity. Qed.
Example fma_is_one_rounding : fma_reference (Atom F32 3212836864)
 (Atom F32 1065353217) (Atom F32 1065353215) = Some (Atom F32 864026622).
Proof. vm_compute; reflexivity. Qed.
Example signed_division_truncates : binary_reference Divide (Atom I32 4294967289)
 (Atom I32 3) = Some (Atom I32 4294967294).
Proof. vm_compute; reflexivity. Qed.
End ReferenceArithmetic.
