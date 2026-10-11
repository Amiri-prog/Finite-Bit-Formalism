(** Coq/FBF_Geometry.v
    Basic geometric structures in FBF
*)

Require Import Coq.Reals.Reals.
Require Import FBF_Basics.

Module Geometry.

Import FBF.

(* Points are abstract for now *)
Parameter Point : Type.

(* Triangle structure *)
Record Triangle := {
  A : Point;
  B : Point;
  C : Point;
}.

(* Sample function: Adjoin a median *)
Parameter adjoin_median : Triangle -> Bit.

End Geometry.
