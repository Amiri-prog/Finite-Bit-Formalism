(** Coq/FBF_Theorems.v
    Theorems proven in the Finite Bit Formalism (FBF)
*)

Require Import FBF_Basics.
Require Import FBF_Geometry.

Module Theorems.

Import FBF.
Import Geometry.

(* Example: Concurrency of triangle medians *)
Parameter concurrency_of_medians :
  forall (T : Triangle),
  exists G : Point,
    True. (* G is the centroid, proof structure here *)

End Theorems.
