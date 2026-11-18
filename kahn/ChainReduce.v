From Stdlib Require Import List Arith Bool.
From Kahn Require Import Spec Kahn.
Import ListNotations.

(** * The chain-reduction kernel

    The SpaDA paper's [chain_reduce] (README.md), transcribed into the
    framework statement by statement. PE [i] receives its vector from host
    stream [a_in[i]]; partial sums flow west from PE [K-1], alternating between
    the red and blue streams; PE 0 sends the total to [out[0]].

    Two relay versions: [Original] (the paper) and [RecvFirst], which receives
    the whole partial sum before adding and avoids a SpaDA lowering bug. *)

(** ** Streams and buffers *)
Inductive color := Red | Blue.
(** [Link c p] is the colour-[c] stream from PE [p] to PE [p-1]. *)
Inductive chan := HostIn (i : nat) | HostOut (i : nat) | Link (c : color) (sender : nat).
Definition chan_eq_dec (a b : chan) : {a = b} + {a <> b}.
Proof. decide equality; try apply Nat.eq_dec; decide equality. Defined.
Arguments chan_eq_dec : simpl never.
#[export] Instance chan_dec : Dec chan := chan_eq_dec.

(** [BufA] is the PE's vector [a]; [BufT] is the receive-first buffer [t]. *)
Inductive buf := BufA | BufT.
Definition buf_eq_dec (a b : buf) : {a = b} + {a <> b}.
Proof. decide equality. Defined.
#[export] Instance buf_dec : Dec buf := buf_eq_dec.

(** ** Per-PE code *)
Inductive variant := Original | RecvFirst.

(** Colour PE [K-1] sends on: [red if (K-1) % 2 == 0 else blue]. *)
Definition east_color K := if Nat.even (K - 1) then Red else Blue.
(** Colour PE [i] sends on / receives from. *)
Definition out_color K i := if i =? K - 1 then east_color K else if Nat.odd i then Blue else Red.
Definition in_color i := if i =? 0 then Blue else if Nat.odd i then Red else Blue.

(** Phase 1: [await receive(a, a_in[i])]. *)
Definition phase1 i := [RecvBuf BufA (HostIn i)].
(** East corner: [await send(a, east_color)]. *)
Definition east K i := [SendBuf BufA (Link (east_color K) i)].
Definition relay v n i cin cout :=
  match v with
  (** [await foreach k, x in [0:n], receive(cin) { a[k] = a[k] + x; await send(a[k], cout) }] *)
  | Original => [Loop n (Some (Link cin (S i)))
                  [AssignK BufA (Add (ElemK BufA) X); SendExpr (ElemK BufA) (Link cout i)]]
  (** [await receive(t, cin); map k in [0:n] { a[k] = a[k] + t[k] }; send(a, cout)] *)
  | RecvFirst => [RecvBuf BufT (Link cin (S i));
                  Loop n None [AssignK BufA (Add (ElemK BufA) (ElemK BufT))];
                  SendBuf BufA (Link cout i)]
  end.
(** West corner: [await foreach k, x in [0:n], receive(blue) { a[k] = a[k] + x };
    await send(a, out[0])]. *)
Definition root n := [Loop n (Some (Link Blue 1)) [AssignK BufA (Add (ElemK BufA) X)];
                      SendBuf BufA (HostOut 0)].

(** Subgrids [1:K-1:2] and [2:K-1:2]. *)
Definition odd_pe K i := (1 <=? i) && (i <? K - 1) && Nat.odd i.
Definition even_pe K i := (2 <=? i) && (i <? K - 1) && Nat.even i.

(** PE [i] runs, in block order, every compute block whose subgrid contains it. *)
Definition process v K n i :=
  phase1 i ++
  (if i =? K - 1 then east K i else []) ++
  (if odd_pe K i then relay v n i Red Blue else []) ++
  (if even_pe K i then relay v n i Blue Red else []) ++
  (if i =? 0 then root n else []).

(** ** Inputs and schedule *)
Definition initial_store {V} (inputs : list (list V)) : chan -> list V :=
  fun c => match c with HostIn i => nth i inputs [] | _ => [] end.

(** PEs [i, i-1, ..., 0]: each producer before its consumer. *)
Fixpoint down_from (i : nat) : list nat :=
  match i with O => [0] | S j => S j :: down_from j end.
