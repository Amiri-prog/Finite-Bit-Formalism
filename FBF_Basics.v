(** Coq/FBF_Basics.v
    Basic definitions and axioms for Finite Bit Formalism (FBF)
*)

Require Import Coq.Lists.List.
Import ListNotations.

Module FBF.

(* Basic type for Bits *)
Inductive Bit : Type :=
| LengthBit : nat -> Bit
| RatioBit : nat -> nat -> Bit
| AngleBit : nat -> Bit.

(* Context: finite list of bits *)
Definition Context := list Bit.

(* Axiom 1: Bit Invariance — Contexts are finite and closed under derivation *)
Axiom bit_invariance :
  forall (Γ : Context), exists n, length Γ <= n.

(* Axiom 2: Adjoining a bit may induce new dependent (equivalent) bits *)
Axiom bit_adjoin :
  forall (Γ : Context) (b_ad : Bit),
  exists eq_bits : list Bit, (* equivalent bits *)
    True.  (* Placeholding logical condition *)

(* Axiom 3: Each adjoined bit induces a unique equivalence class *)
Axiom uniqueness_of_equivalents :
  forall (Γ : Context) (b_ad : Bit),
  exists! eq_class : list Bit,
    True.

End FBF.
