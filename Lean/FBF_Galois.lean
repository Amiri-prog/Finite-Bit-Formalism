import FBF_Symmetry

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Algebra.Group.End
import Mathlib.Data.Finite.Perm

-- ============================================
-- PART 16:
-- FBF--GALOIS CORRESPONDENCE
-- ============================================

/-
This section gives the classical Galois realization
of the FBF information--symmetry correspondence.

For a finite Galois extension L/K:

  * an intermediate field F is interpreted as a
    closed information context;

  * F.fixingSubgroup is interpreted as the residual
    symmetry preserving that information;

  * increasing the closed information decreases the
    residual symmetry;

  * the lattice of intermediate fields is
    order-anti-isomorphic to the subgroup lattice
    of Gal(L/K).

These are classical Galois results supplied by Mathlib.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 16.1 Closed information contexts
-- --------------------------------------------

/-
In the Galois realization, a closed FBF information
context is represented by an intermediate field

      K ⊆ F ⊆ L.
-/

abbrev ClosedInformationContext
    (K L : Type*)
    [Field K]
    [Field L]
    [Algebra K L] :=
  IntermediateField K L


-- --------------------------------------------
-- 16.2 Residual symmetry
-- --------------------------------------------

/-
The residual symmetry associated with a closed
information context F is the subgroup of Gal(L/K)
that fixes every element of F.
-/

def ResidualSymmetry
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    (F : ClosedInformationContext K L) :
    Subgroup Gal(L/K) :=
  F.fixingSubgroup


-- --------------------------------------------
-- 16.3 More information gives less symmetry
-- --------------------------------------------

theorem FBF_more_information_less_symmetry
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    {F₁ F₂ : ClosedInformationContext K L}
    (h : F₁ ≤ F₂) :
    ResidualSymmetry F₂ ≤
    ResidualSymmetry F₁ := by

  exact
    IntermediateField.fixingSubgroup_le h


-- --------------------------------------------
-- 16.4 Joining information intersects symmetries
-- --------------------------------------------

theorem FBF_information_join_symmetry_meet
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    (F₁ F₂ : ClosedInformationContext K L) :
    ResidualSymmetry (F₁ ⊔ F₂) =
      ResidualSymmetry F₁ ⊓
      ResidualSymmetry F₂ := by

  exact
    IntermediateField.fixingSubgroup_sup


-- --------------------------------------------
-- 16.5 Full Galois anti-isomorphism
-- --------------------------------------------

/-
For a finite Galois extension L/K, the complete
lattice of closed information contexts is
order-anti-isomorphic to the subgroup lattice
of Gal(L/K).
-/

noncomputable def FBF_GaloisAntiIso
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L] :
    IntermediateField K L ≃o
      (Subgroup Gal(L/K))ᵒᵈ :=

  IsGalois.intermediateFieldEquivSubgroup


-- --------------------------------------------
-- --------------------------------------------
-- 16.6 Meaning of the forward correspondence
-- --------------------------------------------

theorem FBF_GaloisAntiIso_apply
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    (F : IntermediateField K L) :
    OrderDual.ofDual
      (FBF_GaloisAntiIso F) =
        F.fixingSubgroup := by

  simp [FBF_GaloisAntiIso]

-- --------------------------------------------
-- 16.7 Fixed field recovers the information context
-- --------------------------------------------

/-
For a finite Galois extension, taking the fixed field
of the residual symmetry recovers exactly the original
closed information context.
-/

theorem FBF_information_recovered_from_symmetry
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    (F : IntermediateField K L) :
    IntermediateField.fixedField
        F.fixingSubgroup =
      F := by

  exact
    IsGalois.fixedField_fixingSubgroup F


-- --------------------------------------------
-- 16.8 A subgroup is recovered from its invariant
--      information
-- --------------------------------------------

/-
Conversely, beginning with a subgroup H, taking its
fixed field and then the subgroup fixing that field
recovers H.
-/

theorem FBF_symmetry_recovered_from_information
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    (H : Subgroup Gal(L/K)) :
    (IntermediateField.fixedField H).fixingSubgroup =
      H := by

  exact
    IntermediateField.fixingSubgroup_fixedField H


-- --------------------------------------------
-- 16.9 Extreme information states
-- --------------------------------------------

/-
The full extension field contains maximal information,
so its residual symmetry is trivial.
-/

theorem FBF_full_information_trivial_symmetry
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L] :
    ResidualSymmetry
      (⊤ : IntermediateField K L) =
      ⊥ := by

  exact
    IntermediateField.fixingSubgroup_top


/-
The base-field information contains no additional
extension information, so every Galois automorphism
preserves it.
-/

theorem FBF_base_information_full_symmetry
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L] :
    ResidualSymmetry
      (⊥ : IntermediateField K L) =
      ⊤ := by

  exact
    IntermediateField.fixingSubgroup_bot


-- --------------------------------------------
-- 16.10 Explicit FBF correspondence theorem
-- --------------------------------------------

theorem FBF_Galois_information_symmetry_correspondence
    {K L : Type*}
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L] :
    ∃ e :
      IntermediateField K L ≃o
        (Subgroup Gal(L/K))ᵒᵈ,
      ∀ F : IntermediateField K L,
        OrderDual.ofDual (e F) =
          F.fixingSubgroup := by

  refine
    ⟨FBF_GaloisAntiIso, ?_⟩

  intro F

  exact
    FBF_GaloisAntiIso_apply F


end FBF_Galois


-- ============================================
-- PART 16.11:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 17:
-- POLYNOMIAL ROOT BITS AND GALOIS ACTION
-- ============================================

/-
This section realizes the atomic level of the
FBF--Galois correspondence.

For a polynomial p over a field F:

  * the roots in the splitting field form the
    atomic semantic root-information units;

  * Gal(p) acts on those roots;

  * this action is faithful;

  * if p is irreducible, the action is transitive;

  * therefore, after choosing a root r,

        roots(p) ≃ Gal(p) / Stab(r).

This is the formal root-bit / coset correspondence.
-/


namespace FBF_Galois
-- --------------------------------------------
-- 17.0 Polynomial splits in its splitting field
-- --------------------------------------------

/-
Mathlib's generic Galois-action API asks for the
splitting property wrapped as a `Fact`.

For p.SplittingField this property follows directly
from the defining IsSplittingField instance.
-/

noncomputable local instance
    polynomialSplittingFieldSplitsFact
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    Fact
      (Polynomial.map
        (algebraMap F p.SplittingField)
        p).Splits :=

  ⟨Polynomial.IsSplittingField.splits
      p.SplittingField
      p⟩
-- --------------------------------------------
-- 17.1 Root-information type
-- --------------------------------------------

/-
The roots of p in its splitting field are treated
as the atomic root-information units.

This type is a subtype: an element contains both
a value in the splitting field and the proof that
it is a root of p.
-/

abbrev PolynomialRoot
    {F : Type*}
    [Field F]
    (p : Polynomial F) :=
  ↥(p.rootSet p.SplittingField)


-- --------------------------------------------
-- 17.1a Use one canonical Galois action
--      throughout the FBF root construction
-- --------------------------------------------

/-
For roots in p.SplittingField, Mathlib provides both
galActionAux and the generic galAction specialized to
p.SplittingField.

They represent the same mathematical Galois action,
but Lean treats them as distinct typeclass instances.

For the FBF construction we use the generic
galAction p p.SplittingField consistently.
-/

noncomputable local instance
    polynomialRootSMul
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    SMul p.Gal (PolynomialRoot p) :=
  Polynomial.Gal.smul
    p
    p.SplittingField


noncomputable local instance
    polynomialRootMulAction
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    MulAction p.Gal (PolynomialRoot p) :=
  Polynomial.Gal.galAction
    p
    p.SplittingField

-- --------------------------------------------
-- 17.2 Governing polynomial Galois group
-- --------------------------------------------

/-
Mathlib defines p.Gal as the automorphism group
of the splitting field of p over F.
-/

abbrev PolynomialGoverningGroup
    {F : Type*}
    [Field F]
    (p : Polynomial F) :=
  p.Gal


-- --------------------------------------------
-- 17.3 Galois action on root information
-- --------------------------------------------

/-
The Galois group acts on the roots by permutation.

The result is expressed explicitly as a group
homomorphism into the permutation group of the
root-information type.
-/

noncomputable def PolynomialRootAction
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    p.Gal →*
      Equiv.Perm (PolynomialRoot p) :=

  Polynomial.Gal.galActionHom
    p
    p.SplittingField


-- --------------------------------------------
-- 17.4 Faithfulness of the root action
-- --------------------------------------------

/-
Different elements of the polynomial Galois group
induce different permutations of the complete root
set.

Thus the governing symmetry is faithfully represented
by its action on the root information.
-/

theorem PolynomialRootAction_faithful
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    Function.Injective
      (PolynomialRootAction p) := by

  exact
    Polynomial.Gal.galActionHom_injective
      p
      p.SplittingField


-- --------------------------------------------
-- 17.5 Irreducibility gives transitivity
-- --------------------------------------------

/-
For an irreducible polynomial, every root is a
Galois conjugate of every other root.

Hence the Galois action on the root-information
units is pretransitive.
-/

theorem PolynomialRootAction_pretransitive
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p) :
    MulAction.IsPretransitive
      p.Gal
      (PolynomialRoot p) := by

  exact
    Polynomial.Gal.galAction_isPretransitive
      p
      p.SplittingField
      hp


-- --------------------------------------------
-- 17.6 Every root is obtained from a chosen root
-- --------------------------------------------

theorem every_root_from_chosen_root
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r s : PolynomialRoot p) :
    ∃ g : p.Gal,
      g • r = s := by

  have hpre :
      MulAction.IsPretransitive
        p.Gal
        (PolynomialRoot p) :=
    PolynomialRootAction_pretransitive p hp

  exact
    hpre.exists_smul_eq r s


-- --------------------------------------------
-- 17.7 The orbit of a root is the full root set
-- --------------------------------------------

theorem root_orbit_eq_univ
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :
    MulAction.orbit p.Gal r =
      Set.univ := by

  have hpre :
      MulAction.IsPretransitive
        p.Gal
        (PolynomialRoot p) :=
    PolynomialRootAction_pretransitive p hp

  exact
    (MulAction.isPretransitive_iff_orbit_eq_univ r).mp
      hpre


-- --------------------------------------------
-- 17.8 Orbit--stabilizer equivalence
-- --------------------------------------------

/-
For any chosen root r, independently of
irreducibility, the orbit of r is equivalent to
the quotient of the governing Galois group by the
stabilizer of r.
-/

noncomputable def rootOrbitEquivQuotientStabilizer
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (r : PolynomialRoot p) :

    ↥(MulAction.orbit p.Gal r)
      ≃
    p.Gal ⧸
      MulAction.stabilizer p.Gal r :=

  MulAction.orbitEquivQuotientStabilizer
    p.Gal
    r


-- --------------------------------------------
-- 17.9 For irreducible p, roots equal the orbit
-- --------------------------------------------

/-
If p is irreducible, the orbit of a chosen root is
the entire root set.

We first construct the explicit equivalence between
the complete root-information type and the orbit
subtype.
-/

noncomputable def rootsEquivOrbit
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    PolynomialRoot p
      ≃
    ↥(MulAction.orbit p.Gal r) where

  toFun := fun x =>
    ⟨x, by
      rw [root_orbit_eq_univ p hp r]
      exact Set.mem_univ x⟩

  invFun := fun x =>
    x.1

  left_inv := by
    intro x
    rfl

  right_inv := by
    intro x
    cases x
    rfl


-- --------------------------------------------
-- 17.10 Atomic root-bit / coset correspondence
-- --------------------------------------------

/-
Combining:

  roots(p) ≃ orbit(r)

with the orbit--stabilizer theorem

  orbit(r) ≃ Gal(p) / Stab(r),

we obtain the atomic FBF--Galois correspondence

  B_R ≃ G / Stab_G(r).

This is the precise formal version of the statement
that a semantic root bit corresponds to a coset of
automorphisms having the same action on a selected
root.
-/

noncomputable def
    irreducibleRootsEquivQuotientStabilizer
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    PolynomialRoot p
      ≃
    p.Gal ⧸
      MulAction.stabilizer p.Gal r :=

  (rootsEquivOrbit p hp r).trans
    (rootOrbitEquivQuotientStabilizer p r)


-- --------------------------------------------
-- 17.11 Explicit root--coset theorem
-- --------------------------------------------

theorem FBF_atomic_root_coset_correspondence
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    Nonempty
      (PolynomialRoot p
        ≃
       p.Gal ⧸
        MulAction.stabilizer p.Gal r) := by

  exact
    ⟨irreducibleRootsEquivQuotientStabilizer
      p hp r⟩


-- --------------------------------------------
-- 17.12 Root count equals coset count
-- --------------------------------------------

/-
Because the two types are equivalent, their finite
cardinalities agree.

This realizes the information-count form of the
atomic correspondence.
-/

theorem root_count_eq_coset_count
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    Nat.card (PolynomialRoot p) =
    Nat.card
      (p.Gal ⧸
        MulAction.stabilizer p.Gal r) := by

  exact
    Nat.card_congr
      (irreducibleRootsEquivQuotientStabilizer
        p hp r)


end FBF_Galois


-- ============================================
-- PART 17.13:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 18:
-- POLYNOMIAL ROOTS AS AN FBF BIT-SYMMETRY
-- REALIZATION
-- ============================================

/-
Part 17 established the genuine Galois action

        Gal(p) ↷ PolynomialRoot p

and, for irreducible p,

        PolynomialRoot p
            ≃
        Gal(p) / Stab(r).

Part 18 connects this classical structure to the
abstract FBFBitSymmetry introduced in Part 11.

A semantic labeling identifies each polynomial root
with exactly one atomic FBF bit.

The Galois action is then transported through this
equivalence, producing an actual FBFBitSymmetry.
-/


namespace FBF_Galois

-- --------------------------------------------
-- 18.0 Use the same Galois root action as Part 17
-- --------------------------------------------

/-
Part 17 used the generic Galois action on the roots
in p.SplittingField.

Because the corresponding instances were local to
Part 17, we reinstall the same action locally here.
This prevents Lean from reverting to galActionAux.
-/

noncomputable local instance
    part18PolynomialSplittingFieldSplitsFact
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    Fact
      (Polynomial.map
        (algebraMap F p.SplittingField)
        p).Splits :=
  ⟨Polynomial.IsSplittingField.splits
      p.SplittingField
      p⟩


noncomputable local instance
    part18PolynomialRootSMul
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    SMul p.Gal (PolynomialRoot p) :=
  Polynomial.Gal.smul
    p
    p.SplittingField


noncomputable local instance
    part18PolynomialRootMulAction
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    MulAction p.Gal (PolynomialRoot p) :=
  Polynomial.Gal.galAction
    p
    p.SplittingField
-- --------------------------------------------
-- 18.1 Semantic root-bit realization
-- --------------------------------------------

/-
A PolynomialRootBitRealization consists of:

  * an FBF information set A;
  * a one-to-one correspondence between the actual
    polynomial roots and the atomic FBF bits in A.

Thus the semantic root bits are not identified with
their numerical/algebraic values.  They are labeled
information units corresponding bijectively to them.
-/

structure PolynomialRootBitRealization
    {F : Type*}
    [Field F]
    (p : Polynomial F) where

  bits :
    InformationSet

  labeling :
    PolynomialRoot p ≃
      AdjoinedAtom bits


-- --------------------------------------------
-- 18.2 Transport the Galois action to FBF bits
-- --------------------------------------------

/-
If

        e : roots(p) ≃ FBF bits,

then a permutation σ of the roots induces the
conjugate permutation

        e ∘ σ ∘ e⁻¹

of the FBF bits.

Equiv.permCongrHom performs exactly this transport.
-/

noncomputable def transportedRootBitAction
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p) :

    p.Gal →*
      Equiv.Perm (AdjoinedAtom R.bits) :=

  R.labeling.permCongrHom.toMonoidHom.comp
    (PolynomialRootAction p)


-- --------------------------------------------
-- 18.3 Faithfulness survives semantic labeling
-- --------------------------------------------

/-
Part 17 proved that the Galois action on the actual
roots is faithful.

Since the semantic labeling is an equivalence,
transporting the action through that equivalence
cannot identify two distinct Galois automorphisms.
-/

theorem transportedRootBitAction_faithful
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p) :

    Function.Injective
      (transportedRootBitAction R) := by

  exact
    R.labeling.permCongrHom.injective.comp
      (PolynomialRootAction_faithful p)


-- --------------------------------------------
-- 18.4 Polynomial root system gives an
--      FBFBitSymmetry
-- --------------------------------------------

/-
This is the principal bridge theorem of Part 18.

The polynomial Galois root system is now an instance
of the abstract FBF bit-symmetry structure introduced
in Part 11.
-/

noncomputable def PolynomialFBFBitSymmetry
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p) :

    FBFBitSymmetry
      R.bits
      p.Gal where

  action :=
    transportedRootBitAction R

  faithful :=
    transportedRootBitAction_faithful R


-- --------------------------------------------
-- 18.5 Explicit compatibility of root action
--      and semantic-bit action
-- --------------------------------------------

/-
If r is a polynomial root and g is a Galois
automorphism, then:

  1. act on r by g and then label the resulting root;

is identical to:

  2. label r first and then act on its FBF bit.

Thus the semantic labeling is equivariant.
-/

theorem PolynomialFBFBitSymmetry_equivariant
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p)
    (g : p.Gal)
    (r : PolynomialRoot p) :

    (PolynomialFBFBitSymmetry R).action
        g
        (R.labeling r)
      =
    R.labeling
      ((PolynomialRootAction p g) r) := by

  simp
    [PolynomialFBFBitSymmetry,
     transportedRootBitAction]


-- --------------------------------------------
-- 18.6 Recovering a root from its semantic bit
-- --------------------------------------------

noncomputable def rootOfSemanticBit
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p) :

    AdjoinedAtom R.bits →
      PolynomialRoot p :=

  R.labeling.symm


theorem rootOfSemanticBit_labeling
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p)
    (r : PolynomialRoot p) :

    rootOfSemanticBit R
      (R.labeling r) =
    r := by

  simp [rootOfSemanticBit]


-- --------------------------------------------
-- 18.7 Root-bit / coset correspondence
--      in FBF form
-- --------------------------------------------

/-
Part 17 proved

        roots(p) ≃ Gal(p) / Stab(r).

Since the roots are now bijectively represented by
the FBF semantic bits, we obtain

        FBF root bits ≃ Gal(p) / Stab(r).

This is the atomic FBF--Galois correspondence in
the language of the abstract Bit structure.
-/

noncomputable def
    FBFRootBitsEquivQuotientStabilizer
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    AdjoinedAtom R.bits
      ≃
    p.Gal ⧸
      MulAction.stabilizer p.Gal r :=

  R.labeling.symm.trans
    (irreducibleRootsEquivQuotientStabilizer
      p hp r)


-- --------------------------------------------
-- 18.8 Explicit FBF atomic correspondence theorem
-- --------------------------------------------

theorem FBF_semantic_bits_coset_correspondence
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    Nonempty
      (AdjoinedAtom R.bits
        ≃
       p.Gal ⧸
        MulAction.stabilizer p.Gal r) := by

  exact
    ⟨FBFRootBitsEquivQuotientStabilizer
      R hp r⟩


-- --------------------------------------------
-- 18.9 Cardinality of semantic root bits
-- --------------------------------------------

theorem semantic_root_bit_count_eq_coset_count
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p)
    (hp : Irreducible p)
    (r : PolynomialRoot p) :

    Nat.card
        (AdjoinedAtom R.bits)
      =
    Nat.card
      (p.Gal ⧸
        MulAction.stabilizer p.Gal r) := by

  exact
    Nat.card_congr
      (FBFRootBitsEquivQuotientStabilizer
        R hp r)


-- --------------------------------------------
-- 18.10 Semantic root-bit count equals
--       actual root count
-- --------------------------------------------

theorem semantic_root_bit_count_eq_root_count
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialRootBitRealization p) :

    Nat.card
        (AdjoinedAtom R.bits)
      =
    Nat.card
        (PolynomialRoot p) := by

  exact
    Nat.card_congr
      R.labeling.symm


end FBF_Galois


-- ============================================
-- PART 18.11:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 19:
-- FBF EMERGENCE IN THE POLYNOMIAL REALIZATION
-- ============================================

/-
Parts 16--18 established the classical mathematical
structure independently of FBF axioms:

    Gal(p) acts faithfully on the roots,

    semantic FBF root bits carry the transported
    Galois action,

and, for irreducible p,

    B_R ≃ Gal(p) / Stab(r).

Part 19 is the first point where this classical
structure is joined explicitly to the FBF axioms.

Because InformationStructure.Realizes,
BitDependency.Dependent, and
InformationEquivalence.Equivalent are abstract FBF
relations, Galois theory alone does not prove that
the root-bit set is a determining adjoined set or
that a particular equivalent set is a minimal
equivalent representation.

These properties are therefore recorded as the
FBF realization hypotheses.  Axioms 1 and 3 then
derive interchangeability, emergence, bit balance,
and uniqueness of the emergent theorem.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 19.1 Polynomial FBF emergence realization
-- --------------------------------------------

structure PolynomialFBFEmergenceRealization
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F : Type*}
    [Field F]
    (p : Polynomial F) where

  -- Semantic root-bit realization from Part 18.
  roots :
    PolynomialRootBitRealization p

  -- The mathematical entity described by the
  -- complete FBF information structure.
  entity :
    FObject

  -- Existing information before adjoining roots.
  baseBits :
    InformationSet

  -- A chosen minimal equivalent representation
  -- of the information introduced by the roots.
  equivalentBits :
    InformationSet

  -- The semantic root bits are a minimal determining
  -- independent adjoined set relative to baseBits.
  rootsDetermining :
    DeterminingAdjoinedBits
      baseBits
      roots.bits
      entity

  -- The chosen equivalent bits form a minimal
  -- equivalent representation of the root-bit
  -- information.
  equivalentMinimal :
    MinimalEquivalentBits
      entity
      baseBits
      roots.bits
      equivalentBits


-- --------------------------------------------
-- 19.2 Root bits are genuine adjoined bits
-- --------------------------------------------

theorem PolynomialFBF_roots_are_adjoined
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    AdjoinedBits
      R.baseBits
      R.roots.bits := by

  exact
    determiningAdjoinedBits_implies_adjoinedBits
      R.rootsDetermining


-- --------------------------------------------
-- 19.3 Axiom 1:
--      root information and equivalent information
--      are interchangeable
-- --------------------------------------------

theorem PolynomialFBF_equivalent_interchange
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom1]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    EquivalentSet
        R.entity
        (AdjoinSet
          R.baseBits
          R.roots.bits)
        (AdjoinSet
          R.baseBits
          R.equivalentBits)
      ∧
    EquivalentSet
        R.entity
        (AdjoinSet
          R.baseBits
          R.equivalentBits)
        (AdjoinSet
          R.baseBits
          R.roots.bits) := by

  exact
    FBF_minimal_equivalent_interchange
      R.equivalentMinimal


-- --------------------------------------------
-- 19.4 Refined Axiom 3:
--      emergence of an equivalent representation
-- --------------------------------------------

theorem PolynomialFBF_equivalent_emerges
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    ∃ E : InformationSet,
      MinimalEquivalentBits
        R.entity
        R.baseBits
        R.roots.bits
        E := by

  exact
    FBF_Axiom3_Refined.emergence
      R.entity
      R.baseBits
      R.roots.bits
      R.rootsDetermining


-- --------------------------------------------
-- 19.5 Refined Axiom 3:
--      bit balance
-- --------------------------------------------

theorem PolynomialFBF_bit_balance
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    BitContent R.roots.bits =
    BitContent R.equivalentBits := by

  exact
    FBF_bit_balance
      R.rootsDetermining
      R.equivalentMinimal


-- --------------------------------------------
-- 19.6 Every minimal equivalent representation
--      has the same bit count
-- --------------------------------------------

theorem PolynomialFBF_all_equivalents_balanced
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p)
    (E : InformationSet)
    (hE :
      MinimalEquivalentBits
        R.entity
        R.baseBits
        R.roots.bits
        E) :

    BitContent R.roots.bits =
    BitContent E := by

  exact
    FBF_Axiom3_Refined.bit_balance
      R.entity
      R.baseBits
      R.roots.bits
      E
      R.rootsDetermining
      hE


-- --------------------------------------------
-- 19.7 Refined Axiom 3:
--      uniqueness of the emergent theorem
-- --------------------------------------------

theorem PolynomialFBF_emergent_theorem_unique
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    ∃! T :
      FBF_Axiom3_Refined.EmergentTheoremType,

      ∀ E : InformationSet,
        MinimalEquivalentBits
          R.entity
          R.baseBits
          R.roots.bits
          E →

        FBF_Axiom3_Refined.Relates
          T
          R.entity
          R.baseBits
          R.roots.bits
          E := by

  exact
    FBF_Axiom3_Refined.emergent_theorem_unique
      R.entity
      R.baseBits
      R.roots.bits
      R.rootsDetermining


-- --------------------------------------------
-- 19.8 The chosen equivalent representation
--      belongs to the unique emergent theorem class
-- --------------------------------------------

theorem PolynomialFBF_chosen_equivalent_related
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    ∃ T :
      FBF_Axiom3_Refined.EmergentTheoremType,

      FBF_Axiom3_Refined.Relates
        T
        R.entity
        R.baseBits
        R.roots.bits
        R.equivalentBits := by

  obtain ⟨T, hT, hUnique⟩ :=
    PolynomialFBF_emergent_theorem_unique R

  refine ⟨T, ?_⟩

  exact
    hT
      R.equivalentBits
      R.equivalentMinimal


-- --------------------------------------------
-- 19.9 Complete FBF emergence package
-- --------------------------------------------

theorem PolynomialFBF_emergence_package
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom1]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialFBFEmergenceRealization p) :

    AdjoinedBits
        R.baseBits
        R.roots.bits

    ∧

    BitContent R.roots.bits =
        BitContent R.equivalentBits

    ∧

    EquivalentSet
        R.entity
        (AdjoinSet
          R.baseBits
          R.roots.bits)
        (AdjoinSet
          R.baseBits
          R.equivalentBits)

    ∧

    EquivalentSet
        R.entity
        (AdjoinSet
          R.baseBits
          R.equivalentBits)
        (AdjoinSet
          R.baseBits
          R.roots.bits)

    ∧

    ∃ T :
      FBF_Axiom3_Refined.EmergentTheoremType,

      FBF_Axiom3_Refined.Relates
        T
        R.entity
        R.baseBits
        R.roots.bits
        R.equivalentBits := by

  have hAdj :
      AdjoinedBits
        R.baseBits
        R.roots.bits :=
    PolynomialFBF_roots_are_adjoined R

  have hBal :
      BitContent R.roots.bits =
      BitContent R.equivalentBits :=
    PolynomialFBF_bit_balance R

  have hEq :=
    PolynomialFBF_equivalent_interchange R

  have hRel :=
    PolynomialFBF_chosen_equivalent_related R

  exact
    ⟨hAdj,
     hBal,
     hEq.1,
     hEq.2,
     hRel⟩


end FBF_Galois


-- ============================================
-- PART 19.10:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 20:
-- VIETA INVARIANT BITS
-- ============================================

/-
Part 19 treated the equivalent information E_R
abstractly.

Part 20 makes that information concrete for the
polynomial realization.

For the polynomial mapped into its splitting field:

  * each non-leading coefficient position is treated
    as a distinct semantic information position;

  * its coefficient value is fixed by every element
    of the Galois group;

  * Vieta's formula expresses that coefficient as
    an elementary symmetric function of the roots;

  * therefore the coefficient bits are invariant
    equivalent information generated from the
    root configuration.

The labels are essential: two coefficient positions
may have the same numerical value (for example,
several zero coefficients) but still represent
different semantic FBF bits.
-/


namespace FBF_Galois

noncomputable section
-- --------------------------------------------
-- 20.1 Polynomial in its splitting field
-- --------------------------------------------

abbrev SplittingPolynomial
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    Polynomial p.SplittingField :=

  p.map
    (algebraMap F p.SplittingField)


theorem splittingPolynomial_splits
    {F : Type*}
    [Field F]
    (p : Polynomial F) :
    (SplittingPolynomial p).Splits := by

  simpa [SplittingPolynomial] using
    (Polynomial.IsSplittingField.splits
      p.SplittingField
      p)


-- --------------------------------------------
-- 20.2 Vieta information positions
-- --------------------------------------------

/-
For a polynomial of degree n, there are n
non-leading coefficient positions:

    0, 1, ..., n-1.

These correspond to the n elementary symmetric
root invariants e_n, ..., e_1.

Using Fin n keeps equal numerical coefficient
values at different positions semantically distinct.
-/

abbrev VietaPosition
    {F : Type*}
    [Field F]
    (p : Polynomial F) :=
  Fin (SplittingPolynomial p).natDegree


-- --------------------------------------------
-- 20.3 Coefficient value attached to a position
-- --------------------------------------------

def MappedCoefficient
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (k : VietaPosition p) :
    p.SplittingField :=

  (SplittingPolynomial p).coeff k.1


-- --------------------------------------------
-- 20.4 Corresponding elementary symmetric
--      root invariant
-- --------------------------------------------

def RootSymmetricInvariant
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (k : VietaPosition p) :
    p.SplittingField :=

  (SplittingPolynomial p).roots.esymm
    ((SplittingPolynomial p).natDegree - k.1)


-- --------------------------------------------
-- 20.5 The mapped coefficient really is the
--      original coefficient embedded into the
--      splitting field
-- --------------------------------------------

theorem MappedCoefficient_eq_algebraMap
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (k : VietaPosition p) :

    MappedCoefficient p k =
      algebraMap F p.SplittingField
        (p.coeff k.1) := by

  simp [MappedCoefficient, SplittingPolynomial]


-- --------------------------------------------
-- 20.6 Coefficient information is Galois invariant
-- --------------------------------------------

/-
Every Galois automorphism fixes the base field.
Therefore every coefficient of p, viewed in the
splitting field, is fixed by Gal(p).
-/

theorem MappedCoefficient_fixed
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (k : VietaPosition p)
    (g : p.Gal) :

    g (MappedCoefficient p k) =
      MappedCoefficient p k := by

  rw [MappedCoefficient_eq_algebraMap]

  exact
    g.commutes (p.coeff k.1)


-- --------------------------------------------
-- 20.7 Vieta's formula
-- --------------------------------------------

/-
Mathlib's Vieta theorem gives

  coeff(k)
    =
  leadingCoeff
    * (-1)^(n-k)
    * e_(n-k)(roots).

This is exactly the root-information to
coefficient-information map required by the
polynomial FBF realization.
-/

theorem MappedCoefficient_eq_vieta
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (k : VietaPosition p) :

    MappedCoefficient p k
      =
    (SplittingPolynomial p).leadingCoeff
      *
    (-1) ^
      ((SplittingPolynomial p).natDegree - k.1)
      *
    RootSymmetricInvariant p k := by

  have hk :
      k.1 ≤
        (SplittingPolynomial p).natDegree :=
    Nat.le_of_lt k.2

  simpa
    [MappedCoefficient,
     RootSymmetricInvariant]
    using
      (Polynomial.coeff_eq_esymm_roots_of_splits
        (splittingPolynomial_splits p)
        hk)


-- --------------------------------------------
-- 20.8 Monic polynomial form
-- --------------------------------------------

theorem splittingPolynomial_monic
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : p.Monic) :

    (SplittingPolynomial p).Monic := by

  exact
    hp.map
      (algebraMap F p.SplittingField)


theorem MappedCoefficient_eq_vieta_of_monic
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (hp : p.Monic)
    (k : VietaPosition p) :

    MappedCoefficient p k
      =
    (-1) ^
      ((SplittingPolynomial p).natDegree - k.1)
      *
    RootSymmetricInvariant p k := by

  have hV :=
    MappedCoefficient_eq_vieta p k

  have hLC :
      (SplittingPolynomial p).leadingCoeff = 1 :=
    (splittingPolynomial_monic p hp).leadingCoeff

  rw [hLC, one_mul] at hV

  exact hV


-- --------------------------------------------
-- 20.9 Semantic FBF coefficient-bit realization
-- --------------------------------------------

/-
One distinct FBF semantic bit is assigned to each
non-leading coefficient position.

Thus equal coefficient values do NOT collapse
different coefficient positions.

For x^3 - 2, for example, the coefficient values
at two positions are both zero, but the positions
remain distinct semantic bits.
-/

structure VietaCoefficientBitRealization
    {F : Type*}
    [Field F]
    (p : Polynomial F) where

  bits :
    InformationSet

  labeling :
    VietaPosition p ≃
      AdjoinedAtom bits


-- --------------------------------------------
-- 20.10 Value represented by a Vieta bit
-- --------------------------------------------

def VietaBitValue
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (V : VietaCoefficientBitRealization p)
    (b : AdjoinedAtom V.bits) :
    p.SplittingField :=

  MappedCoefficient
    p
    (V.labeling.symm b)


-- --------------------------------------------
-- 20.11 Every Vieta bit value is Galois invariant
-- --------------------------------------------

theorem VietaBitValue_fixed
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (V : VietaCoefficientBitRealization p)
    (g : p.Gal)
    (b : AdjoinedAtom V.bits) :

    g (VietaBitValue V b) =
      VietaBitValue V b := by

  exact
    MappedCoefficient_fixed
      p
      (V.labeling.symm b)
      g


-- --------------------------------------------
-- 20.12 Every Vieta bit is generated by a
--       symmetric root expression
-- --------------------------------------------

theorem VietaBitValue_eq_root_symmetric_expression
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (V : VietaCoefficientBitRealization p)
    (b : AdjoinedAtom V.bits) :

    VietaBitValue V b
      =
    (SplittingPolynomial p).leadingCoeff
      *
    (-1) ^
      ((SplittingPolynomial p).natDegree -
        (V.labeling.symm b).1)
      *
    RootSymmetricInvariant
      p
      (V.labeling.symm b) := by

  exact
    MappedCoefficient_eq_vieta
      p
      (V.labeling.symm b)


-- --------------------------------------------
-- 20.13 Monic form for each semantic Vieta bit
-- --------------------------------------------

theorem VietaBitValue_eq_root_symmetric_expression_of_monic
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (hp : p.Monic)
    (V : VietaCoefficientBitRealization p)
    (b : AdjoinedAtom V.bits) :

    VietaBitValue V b
      =
    (-1) ^
      ((SplittingPolynomial p).natDegree -
        (V.labeling.symm b).1)
      *
    RootSymmetricInvariant
      p
      (V.labeling.symm b) := by

  exact
    MappedCoefficient_eq_vieta_of_monic
      p hp
      (V.labeling.symm b)


-- --------------------------------------------
-- 20.14 Number of Vieta semantic bits
-- --------------------------------------------

theorem VietaCoefficientBitRealization_bit_count
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (V : VietaCoefficientBitRealization p) :

    BitContent V.bits =
      (SplittingPolynomial p).natDegree := by

  have h :=
    Fintype.card_congr V.labeling

  simpa
    [BitContent,
     VietaPosition,
     AdjoinedAtom]
    using h.symm


-- --------------------------------------------
-- 20.15 Connect Vieta bits to the Part 19
--       equivalent-bit realization
-- --------------------------------------------

/-
The Part 19 equivalent information E_R is now
identified explicitly with the labeled Vieta
coefficient bits.
-/

structure PolynomialVietaFBFRealization
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F : Type*}
    [Field F]
    (p : Polynomial F) where

  emergence :
    PolynomialFBFEmergenceRealization p

  vieta :
    VietaCoefficientBitRealization p

  equivalentBits_eq :
    emergence.equivalentBits =
      vieta.bits


-- --------------------------------------------
-- 20.16 Axiom 3 bit balance becomes
--       root bits = Vieta invariant bits
-- --------------------------------------------

theorem PolynomialVietaFBF_bit_balance
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p) :

    BitContent R.emergence.roots.bits =
      BitContent R.vieta.bits := by

  have h :=
    PolynomialFBF_bit_balance
      R.emergence

  rw [R.equivalentBits_eq] at h

  exact h


-- --------------------------------------------
-- 20.17 Root-bit count equals polynomial degree
-- --------------------------------------------

theorem PolynomialVietaFBF_root_bit_count_eq_degree
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p) :

    BitContent R.emergence.roots.bits =
      (SplittingPolynomial p).natDegree := by

  calc
    BitContent R.emergence.roots.bits
        =
      BitContent R.vieta.bits :=
        PolynomialVietaFBF_bit_balance R

    _ =
      (SplittingPolynomial p).natDegree :=
        VietaCoefficientBitRealization_bit_count
          R.vieta


end
end FBF_Galois


-- ============================================
-- PART 20.18:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 21:
-- RADICAL SOLVABILITY AND THE POLYNOMIAL
-- REFERENCE CRITERION
-- ============================================

/-
Mathlib currently formalizes one direction of the
classical solvability-by-radicals theorem:

    radical root
        =>
    solvable Galois group.

Part 21 connects that established result to the FBF
constructive-biconditionality machinery.

The converse direction is NOT silently assumed.
It is represented below by an explicit named
hypothesis, so Lean will make its use visible.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 21.1 Radical-root witness
-- --------------------------------------------

/-
A polynomial has a radical-root witness in an
extension E if some root x in E belongs to Mathlib's
solvableByRad intermediate field.

The ambient field E is kept general because a
radical expression may naturally live in an
extension larger than the splitting field itself.
-/

def PolynomialRadicalRootWitness
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    (p : Polynomial F) : Prop :=

  ∃ x : E,
    x ∈ solvableByRad F E
      ∧
    (Polynomial.aeval x) p = 0


-- --------------------------------------------
-- 21.2 Mathlib Abel--Ruffini direction
-- --------------------------------------------

/-
For an irreducible polynomial, a radical-root
witness implies that its Galois group is solvable.

This theorem comes from Mathlib's formalized
Abel--Ruffini direction.
-/

theorem radicalRootWitness_gal_isSolvable
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (hRad :
      PolynomialRadicalRootWitness
        (E := E)
        p) :

    Group.IsSolvable p.Gal := by

  rcases hRad with
    ⟨x, hxRad, hxRoot⟩

  exact
    isSolvable_gal_of_irreducible
      hxRad
      hp
      hxRoot


-- --------------------------------------------
-- 21.3 FBF radical soundness
-- --------------------------------------------

/-
This property states that an FBF constructive
reverse really represents a radical reconstruction
in the classical algebraic sense.

It is a bridge condition between:

    EmergentBiconditional

and

    PolynomialRadicalRootWitness.

It does NOT assert the converse.
-/

def PolynomialFBFRadicalSoundness
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem) : Prop :=

  EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits
    →
  PolynomialRadicalRootWitness
      (E := E)
      p


-- --------------------------------------------
-- 21.4 Rigorous direction:
--      FBF biconditionality => solvable symmetry
-- --------------------------------------------

theorem PolynomialFBF_biconditional_implies_solvable
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hBicond :
      EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits) :

    Group.IsSolvable p.Gal := by

  apply
    radicalRootWitness_gal_isSolvable
      (E := E)
      hp

  exact
    hSound hBicond


-- --------------------------------------------
-- 21.5 Contrapositive obstruction theorem
-- --------------------------------------------

/-
This is already enough for the negative side of
the threshold argument.

If the governing Galois group is not solvable,
then no FBF reconstruction satisfying the radical
soundness condition can be constructively
biconditional.
-/

theorem PolynomialFBF_not_biconditional_of_not_solvable
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hNot :
      ¬ Group.IsSolvable p.Gal) :

    ¬ EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits := by

  intro hBicond

  apply hNot

  exact
    PolynomialFBF_biconditional_implies_solvable
      (E := E)
      hp
      R
      C
      hSound
      hBicond


-- ============================================
-- THE CONVERSE SIDE
-- ============================================

/-
The next two definitions keep the still-unformalized
direction completely explicit.

Neither is an FBF axiom.

They are named hypotheses that must eventually be
proved or supplied by the appropriate classical
radical-solvability development.
-/


-- --------------------------------------------
-- 21.6 Classical Galois-to-radical converse
-- --------------------------------------------

def GaloisRadicalConverseAt
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    (p : Polynomial F) : Prop :=

  Group.IsSolvable p.Gal
    →
  PolynomialRadicalRootWitness
    (E := E)
    p


-- --------------------------------------------
-- 21.7 FBF radical completeness
-- --------------------------------------------

/-
If a classical radical reconstruction exists,
this condition says that the chosen FBF construction
system is sufficiently expressive to represent it
as a finite admissible reverse construction.
-/

def PolynomialFBFRadicalCompleteness
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem) : Prop :=

  PolynomialRadicalRootWitness
      (E := E)
      p
    →
  EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits


-- --------------------------------------------
-- 21.8 Solvable symmetry => FBF biconditionality
--      under the explicit converse hypotheses
-- --------------------------------------------

theorem PolynomialFBF_solvable_implies_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C)
    (hSolv :
      Group.IsSolvable p.Gal) :

    EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits := by

  apply hComplete

  exact
    hConverse hSolv


-- --------------------------------------------
-- 21.9 Full polynomial FBF criterion
--      with assumptions exposed
-- --------------------------------------------

theorem PolynomialFBF_solvable_iff_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    Group.IsSolvable p.Gal
      ↔
    EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits := by

  constructor

  · intro hSolv

    exact
      PolynomialFBF_solvable_implies_biconditional
        (E := E)
        R C
        hConverse
        hComplete
        hSolv

  · intro hBicond

    exact
      PolynomialFBF_biconditional_implies_solvable
        (E := E)
        hp
        R C
        hSound
        hBicond


-- --------------------------------------------
-- 21.10 Package as the Part-15 criterion
-- --------------------------------------------

theorem PolynomialFBF_reference_criterion
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    SolvabilityBiconditionalCriterion
      p.Gal
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits := by

  exact
    PolynomialFBF_solvable_iff_biconditional
      (E := E)
      hp
      R
      C
      hSound
      hConverse
      hComplete


end FBF_Galois


-- ============================================
-- PART 21.11:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 22:
-- THE FULL-SYMMETRIC THRESHOLD-4 OBSTRUCTION
-- ============================================

/-
Part 21 established:

    FBF radical biconditionality
        =>
    solvability of the governing Galois group.

Part 22 combines this with the classical fact:

    S_n is not solvable for n >= 5.

Therefore, in a full-symmetric polynomial
realization,

    n >= 5
        =>
    no radical FBF biconditionality.

This proves the rigorous NEGATIVE side of the
threshold-4 principle.

It does NOT yet assert the converse that every
n <= 4 system is biconditional.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 22.1 Symmetric group on n semantic atoms
-- --------------------------------------------

abbrev SymmetricGroupAt (n : ℕ) :=
  Equiv.Perm (Fin n)


-- --------------------------------------------
-- 22.2 Full-symmetric Galois realization
-- --------------------------------------------

/-
The governing Galois group is structurally
isomorphic to the full symmetric group S_n.
-/

def FullSymmetricGaloisAt
    {F : Type*}
    [Field F]
    (p : Polynomial F)
    (n : ℕ) : Prop :=

  Nonempty
    (p.Gal ≃*
      SymmetricGroupAt n)


-- --------------------------------------------
-- 22.3 Classical threshold:
--      S_n is not solvable when n >= 5
-- --------------------------------------------

theorem symmetricGroup_not_solvable_of_five_le
    {n : ℕ}
    (h5 : 5 ≤ n) :

    ¬ Group.IsSolvable
        (SymmetricGroupAt n) := by

  apply
    Equiv.Perm.not_isSolvable
      (Fin n)

  have hCard :
      Cardinal.mk (Fin 5) ≤
        Cardinal.mk (Fin n) := by

    exact
      Cardinal.mk_le_of_injective
        (Fin.castLEEmb h5).injective

  simpa using hCard


-- --------------------------------------------
-- 22.4 Transport non-solvability through
--      a group isomorphism
-- --------------------------------------------

/-
We deliberately use Group.isSolvable_of_surjective
directly rather than the helper theorem from Part 12.

Reason:

    p.Gal

may live in a higher universe, whereas

    Equiv.Perm (Fin n)

lives in Type 0.

The Mathlib theorem below is universe-polymorphic.
-/

theorem fullSymmetricGalois_not_solvable_of_five_le
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    {n : ℕ}
    (hFull :
      FullSymmetricGaloisAt
        p n)
    (h5 : 5 ≤ n) :

    ¬ Group.IsSolvable p.Gal := by

  rcases hFull with
    ⟨e⟩

  intro hGal

  have hSym :
      Group.IsSolvable
        (SymmetricGroupAt n) := by

    exact
      @Group.isSolvable_of_surjective
        p.Gal
        (SymmetricGroupAt n)
        inferInstance
        inferInstance
        e.toMonoidHom
        e.surjective
        hGal

  exact
    (symmetricGroup_not_solvable_of_five_le
      h5)
      hSym


-- --------------------------------------------
-- 22.5 Full-symmetric realization at the
--      polynomial/Vieta degree
-- --------------------------------------------

def FullSymmetricGaloisOnVietaDegree
    {F : Type*}
    [Field F]
    (p : Polynomial F) : Prop :=

  FullSymmetricGaloisAt
    p
    (SplittingPolynomial p).natDegree


-- --------------------------------------------
-- 22.6 Degree >= 5 gives the FBF obstruction
-- --------------------------------------------

theorem PolynomialFBF_fullSymmetric_degree_ge_five_obstruction
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (h5 :
      5 ≤
        (SplittingPolynomial p).natDegree) :

    ¬ EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits := by

  apply
    PolynomialFBF_not_biconditional_of_not_solvable
      (E := E)
      hp
      R
      C
      hSound

  exact
    fullSymmetricGalois_not_solvable_of_five_le
      hFull
      h5


-- --------------------------------------------
-- 22.7 Rewrite the threshold directly in
--      FBF root-bit language
-- --------------------------------------------

theorem PolynomialFBF_fullSymmetric_five_root_bits_obstruction
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (h5bits :
      5 ≤
        BitContent
          R.emergence.roots.bits) :

    ¬ EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits := by

  have hCount :
      BitContent
          R.emergence.roots.bits
        =
      (SplittingPolynomial p).natDegree :=

    PolynomialVietaFBF_root_bit_count_eq_degree
      R

  have h5deg :
      5 ≤
        (SplittingPolynomial p).natDegree := by

    rw [← hCount]

    exact h5bits

  exact
    PolynomialFBF_fullSymmetric_degree_ge_five_obstruction
      (E := E)
      hp
      R
      C
      hSound
      hFull
      h5deg


-- --------------------------------------------
-- 22.8 Threshold-4 theorem:
--      biconditionality forces at most four
--      independent root bits
-- --------------------------------------------

theorem PolynomialFBF_fullSymmetric_biconditional_implies_at_most_four_bits
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (hBicond :
      EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits) :

    BitContent
        R.emergence.roots.bits
      ≤
    4 := by

  by_contra hNot

  have h5 :
      5 ≤
        BitContent
          R.emergence.roots.bits := by
    omega

  have hImpossible :
      ¬ EmergentBiconditional
          C
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits :=

    PolynomialFBF_fullSymmetric_five_root_bits_obstruction
      (E := E)
      hp
      R
      C
      hSound
      hFull
      h5

  exact
    hImpossible hBicond


-- --------------------------------------------
-- 22.9 Degree formulation of the same theorem
-- --------------------------------------------

theorem PolynomialFBF_fullSymmetric_biconditional_implies_degree_le_four
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (hBicond :
      EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits) :

    (SplittingPolynomial p).natDegree
      ≤ 4 := by

  by_contra hNot

  have h5 :
      5 ≤
        (SplittingPolynomial p).natDegree := by
    omega

  have hImpossible :
      ¬ EmergentBiconditional
          C
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits :=

    PolynomialFBF_fullSymmetric_degree_ge_five_obstruction
      (E := E)
      hp
      R
      C
      hSound
      hFull
      h5

  exact
    hImpossible hBicond


end FBF_Galois


-- ============================================
-- PART 22.10:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 23:
-- THE POSITIVE THRESHOLD-4 DIRECTION
-- ============================================

/-
Part 22 proved the negative/obstruction direction:

    full symmetric symmetry
    + radical soundness
    + at least five root bits
        =>
    no FBF biconditionality.

Part 23 proves the classical group-theoretic
positive side:

    S_n is solvable for n <= 4.

We prove:

    S_0, S_1, S_2  by commutativity;

    S_3 using the exact structure
        A_3 -> S_3 -> sign group;

    S_4 by first proving A_4 solvable.
    Mathlib identifies the Klein four subgroup V_4
    with the commutator subgroup of A_4.
    Since V_4 is commutative, it is solvable,
    hence A_4 is solvable, hence S_4 is solvable.

Finally, under the explicit Part-21 assumptions

    GaloisRadicalConverseAt
    PolynomialFBFRadicalCompleteness,

solvability of the full symmetric Galois group
gives FBF biconditionality.

Thus Parts 22 and 23 together give a full
threshold-4 biconditional theorem, conditional
only on the explicitly named radical bridges.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 23.1 S_n is solvable for n <= 2
-- --------------------------------------------

theorem symmetricGroup_solvable_of_le_two
    {n : ℕ}
    (hn : n ≤ 2) :

    Group.IsSolvable
      (SymmetricGroupAt n) := by

  have hComm :
      IsMulCommutative
        (SymmetricGroupAt n) := by

    apply
      (Equiv.Perm.isMulCommutative_iff_card_le_two).2

    simpa using hn

  letI :
      IsMulCommutative
        (SymmetricGroupAt n) :=
    hComm

  infer_instance


-- --------------------------------------------
-- 23.2 A_3 is solvable
-- --------------------------------------------

theorem alternatingGroup_three_solvable :

    Group.IsSolvable
      ↥(alternatingGroup (Fin 3)) := by

  have hComm :
      IsMulCommutative
        ↥(alternatingGroup (Fin 3)) :=

    alternatingGroup.isMulCommutative_of_card_le_three
      (α := Fin 3)
      (by simp)

  letI :
      IsMulCommutative
        ↥(alternatingGroup (Fin 3)) :=
    hComm

  infer_instance


-- --------------------------------------------
-- 23.3 S_3 is solvable
-- --------------------------------------------

/-
The sign homomorphism has kernel A_3.

    A_3 -> S_3 -> {+1,-1}

Both A_3 and the sign group are solvable,
therefore S_3 is solvable.
-/

theorem symmetricGroup_three_solvable :

    Group.IsSolvable
      (SymmetricGroupAt 3) := by

  have hA3 :
      Group.IsSolvable
        ↥(alternatingGroup (Fin 3)) :=
    alternatingGroup_three_solvable

  letI :
      Group.IsSolvable
        ↥(alternatingGroup (Fin 3)) :=
    hA3

  have hSign :
      Group.IsSolvable ℤˣ := by

    exact
      Group.isSolvable_of_comm
        (fun a b => mul_comm a b)

  letI :
      Group.IsSolvable ℤˣ :=
    hSign

  apply
    Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype
      (Equiv.Perm.sign :
        Equiv.Perm (Fin 3) →* ℤˣ)

  rw [
    Subgroup.subtype_range,
    alternatingGroup_eq_sign_ker
  ]


-- --------------------------------------------
-- 23.4 The Klein four subgroup of A_4
--      is solvable
-- --------------------------------------------

theorem alternatingGroup_four_kleinFour_solvable :

    Group.IsSolvable
      ↥(alternatingGroup.kleinFour (Fin 4)) := by

  have hKlein :
      IsKleinFour
        ↥(alternatingGroup.kleinFour (Fin 4)) :=

    alternatingGroup.kleinFour_isKleinFour
      (α := Fin 4)
      (by simp)

  letI :
      IsKleinFour
        ↥(alternatingGroup.kleinFour (Fin 4)) :=
    hKlein

  have hComm :
      IsMulCommutative
        ↥(alternatingGroup.kleinFour (Fin 4)) :=

    IsKleinFour.isMulCommutative

  letI :
      IsMulCommutative
        ↥(alternatingGroup.kleinFour (Fin 4)) :=
    hComm

  infer_instance


-- --------------------------------------------
-- 23.5 A_4 is solvable
-- --------------------------------------------

/-
Mathlib proves, for four letters,

    V_4 = [A_4,A_4].

The commutator subgroup is therefore the
solvable Klein four group.

Mathlib's general theorem

    IsSolvable [G,G] <-> IsSolvable G

then gives solvability of A_4.
-/

theorem alternatingGroup_four_solvable :

    Group.IsSolvable
      ↥(alternatingGroup (Fin 4)) := by

  have hK :
      Group.IsSolvable
        ↥(alternatingGroup.kleinFour (Fin 4)) :=

    alternatingGroup_four_kleinFour_solvable

  have hComm :
      Group.IsSolvable
        ↥(commutator
          ↥(alternatingGroup (Fin 4))) := by

    rw [
      ← alternatingGroup.kleinFour_eq_commutator
          (α := Fin 4)
          (by simp)
    ]

    exact hK

  exact
    (Group.isSolvable_commutator_iff).mp
      hComm


-- --------------------------------------------
-- 23.6 S_4 is solvable
-- --------------------------------------------

/-
Again use the sign exact structure

    A_4 -> S_4 -> {+1,-1}.

A_4 has just been proved solvable.
The sign group is abelian, hence solvable.
-/

theorem symmetricGroup_four_solvable :

    Group.IsSolvable
      (SymmetricGroupAt 4) := by

  have hA4 :
      Group.IsSolvable
        ↥(alternatingGroup (Fin 4)) :=

    alternatingGroup_four_solvable

  letI :
      Group.IsSolvable
        ↥(alternatingGroup (Fin 4)) :=
    hA4

  have hSign :
      Group.IsSolvable ℤˣ := by

    exact
      Group.isSolvable_of_comm
        (fun a b => mul_comm a b)

  letI :
      Group.IsSolvable ℤˣ :=
    hSign

  apply
    Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 4)).subtype
      (Equiv.Perm.sign :
        Equiv.Perm (Fin 4) →* ℤˣ)

  rw [
    Subgroup.subtype_range,
    alternatingGroup_eq_sign_ker
  ]


-- --------------------------------------------
-- 23.7 Complete small-symmetric theorem
-- --------------------------------------------

theorem symmetricGroup_solvable_of_le_four
    {n : ℕ}
    (hn : n ≤ 4) :

    Group.IsSolvable
      (SymmetricGroupAt n) := by

  have hnCases :
      n = 0 ∨
      n = 1 ∨
      n = 2 ∨
      n = 3 ∨
      n = 4 := by
    omega

  rcases hnCases with
      h0 | h1 | h2 | h3 | h4

  · subst n
    exact
      symmetricGroup_solvable_of_le_two
        (by norm_num)

  · subst n
    exact
      symmetricGroup_solvable_of_le_two
        (by norm_num)

  · subst n
    exact
      symmetricGroup_solvable_of_le_two
        (by norm_num)

  · subst n
    exact
      symmetricGroup_three_solvable

  · subst n
    exact
      symmetricGroup_four_solvable


-- --------------------------------------------
-- 23.8 Transport small-symmetric solvability
--      to the polynomial Galois group
-- --------------------------------------------

theorem fullSymmetricGalois_solvable_of_le_four
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    {n : ℕ}
    (hFull :
      FullSymmetricGaloisAt
        p n)
    (h4 : n ≤ 4) :

    Group.IsSolvable
      p.Gal := by

  rcases hFull with
    ⟨e⟩

  have hSym :
      Group.IsSolvable
        (SymmetricGroupAt n) :=

    symmetricGroup_solvable_of_le_four
      h4

  exact
    @Group.isSolvable_of_surjective
      (SymmetricGroupAt n)
      p.Gal
      inferInstance
      inferInstance
      e.symm.toMonoidHom
      e.symm.surjective
      hSym


-- --------------------------------------------
-- 23.9 Degree <= 4:
--      full symmetric Galois group is solvable
-- --------------------------------------------

theorem fullSymmetricGaloisOnVietaDegree_solvable_of_degree_le_four
    {F : Type*}
    [Field F]
    {p : Polynomial F}
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (h4 :
      (SplittingPolynomial p).natDegree ≤ 4) :

    Group.IsSolvable
      p.Gal := by

  exact
    fullSymmetricGalois_solvable_of_le_four
      hFull
      h4


-- --------------------------------------------
-- 23.10 Positive FBF direction:
--       degree <= 4 => biconditionality
-- --------------------------------------------

/-
This is where the two explicit Part-21 bridges
are used:

  1. GaloisRadicalConverseAt:
       solvable Galois group
         =>
       radical reconstruction exists.

  2. PolynomialFBFRadicalCompleteness:
       radical reconstruction
         =>
       FBF reverse construction exists.

They are not hidden axioms.
-/

theorem PolynomialFBF_fullSymmetric_degree_le_four_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (h4 :
      (SplittingPolynomial p).natDegree ≤ 4)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits := by

  have hGal :
      Group.IsSolvable p.Gal :=

    fullSymmetricGaloisOnVietaDegree_solvable_of_degree_le_four
      hFull
      h4

  exact
    PolynomialFBF_solvable_implies_biconditional
      (E := E)
      R
      C
      hConverse
      hComplete
      hGal


-- --------------------------------------------
-- 23.11 Positive FBF direction in root-bit form
-- --------------------------------------------

theorem PolynomialFBF_fullSymmetric_at_most_four_bits_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (h4bits :
      BitContent
        R.emergence.roots.bits ≤ 4)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    EmergentBiconditional
      C
      R.emergence.entity
      R.emergence.baseBits
      R.emergence.roots.bits := by

  have hCount :
      BitContent
          R.emergence.roots.bits
        =
      (SplittingPolynomial p).natDegree :=

    PolynomialVietaFBF_root_bit_count_eq_degree
      R

  have h4deg :
      (SplittingPolynomial p).natDegree ≤ 4 := by

    rw [← hCount]

    exact h4bits

  exact
    PolynomialFBF_fullSymmetric_degree_le_four_biconditional
      (E := E)
      R
      C
      hFull
      h4deg
      hConverse
      hComplete


-- ============================================
-- FULL THRESHOLD-4 SYNTHESIS
-- ============================================


-- --------------------------------------------
-- 23.12 Degree threshold biconditional
-- --------------------------------------------

/-
Combining:

Part 22:
    biconditionality => degree <= 4

Part 23:
    degree <= 4 => biconditionality

gives the full threshold theorem,
provided all bridge assumptions are explicit.
-/

theorem PolynomialFBF_fullSymmetric_threshold_four_degree_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits

      ↔

    (SplittingPolynomial p).natDegree ≤ 4 := by

  constructor

  · intro hBicond

    exact
      PolynomialFBF_fullSymmetric_biconditional_implies_degree_le_four
        (E := E)
        hp
        R
        C
        hSound
        hFull
        hBicond

  · intro h4

    exact
      PolynomialFBF_fullSymmetric_degree_le_four_biconditional
        (E := E)
        R
        C
        hFull
        h4
        hConverse
        hComplete


-- --------------------------------------------
-- 23.13 Root-bit threshold biconditional
-- --------------------------------------------

/-
Using Part 20:

    |B_R| = degree(p),

the degree threshold becomes the direct
FBF bit-count threshold:

    EmergentBiconditional
        <->
    |B_R| <= 4.
-/

theorem PolynomialFBF_fullSymmetric_threshold_four_bits_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    {F E : Type*}
    [Field F]
    [Field E]
    [Algebra F E]
    {p : Polynomial F}
    (hp : Irreducible p)
    (R : PolynomialVietaFBFRealization p)
    (C : FBFConstructionSystem)
    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C)
    (hFull :
      FullSymmetricGaloisOnVietaDegree p)
    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)
    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C) :

    EmergentBiconditional
        C
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits

      ↔

    BitContent
        R.emergence.roots.bits ≤ 4 := by

  constructor

  · intro hBicond

    exact
      PolynomialFBF_fullSymmetric_biconditional_implies_at_most_four_bits
        (E := E)
        hp
        R
        C
        hSound
        hFull
        hBicond

  · intro h4bits

    exact
      PolynomialFBF_fullSymmetric_at_most_four_bits_biconditional
        (E := E)
        R
        C
        hFull
        h4bits
        hConverse
        hComplete


end FBF_Galois


-- ============================================
-- PART 23.14:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 24:
-- STRUCTURAL TRANSFER OF THE
-- POLYNOMIAL THRESHOLD-4 CRITERION
-- ============================================

/-
Parts 21--23 established the polynomial reference
criterion.

For the full-symmetric polynomial realization:

    EmergentBiconditional
        <->
    degree(p) <= 4

under the explicit radical bridge assumptions.

Part 24 now applies the abstract structural
correspondence developed in Parts 14--15.

The central principle is:

    if two FBF realizations have

      * isomorphic governing bit symmetries, and
      * isomorphic admissible construction systems,

    then constructive biconditionality is invariant.

Therefore the threshold theorem established in the
polynomial/Galois realization transfers to any
structurally corresponding FBF realization.

Important:

The target theorem is first expressed relative to
the polynomial reference degree.

We do NOT yet identify this degree with the target
bit count.  That additional cardinality statement
will be proved separately.
-/


namespace FBF_Galois

noncomputable section


-- --------------------------------------------
-- 24.1 Transfer of the complete
--      solvability-biconditionality criterion
-- --------------------------------------------

theorem PolynomialFBF_reference_criterion_transfers
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp : Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}
    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    Group.IsSolvable G₂
      ↔
    EmergentBiconditional
      C₂
      s₂
      (Corr.constructionIso.infoEquiv
        R.emergence.baseBits)
      (Corr.constructionIso.infoEquiv
        R.emergence.roots.bits) := by

  have hRef :
      Group.IsSolvable p.Gal
        ↔
      EmergentBiconditional
        C₁
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits :=

    PolynomialFBF_solvable_iff_biconditional
      (E := E)
      hp
      R
      C₁
      hSound
      hConverse
      hComplete

  have hGroup :
      Group.IsSolvable p.Gal
        ↔
      Group.IsSolvable G₂ :=

    group_solvable_iff_of_mulEquiv
      Corr.symmetryIso.groupEquiv

  have hConstruction :
      EmergentBiconditional
        C₁
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits
        ↔
      EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) :=

    FBF_biconditionality_invariant
      Corr.constructionIso
      R.emergence.baseBits
      R.emergence.roots.bits

  constructor

  · intro hG₂

    have hGal :
        Group.IsSolvable p.Gal :=
      hGroup.mpr hG₂

    have hRefBicond :
        EmergentBiconditional
          C₁
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits :=
      hRef.mp hGal

    exact
      hConstruction.mp hRefBicond

  · intro hTarget

    have hRefBicond :
        EmergentBiconditional
          C₁
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits :=
      hConstruction.mpr hTarget

    have hGal :
        Group.IsSolvable p.Gal :=
      hRef.mpr hRefBicond

    exact
      hGroup.mp hGal


-- --------------------------------------------
-- 24.2 Transfer of the negative
--      degree >= 5 obstruction
-- --------------------------------------------

theorem PolynomialFBF_degree_ge_five_obstruction_transfers
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp : Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    (h5 :
      5 ≤
        (SplittingPolynomial p).natDegree)

    {A₂ : InformationSet}
    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    ¬ EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) := by

  have hReferenceImpossible :
      ¬ EmergentBiconditional
          C₁
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits :=

    PolynomialFBF_fullSymmetric_degree_ge_five_obstruction
      (E := E)
      hp
      R
      C₁
      hSound
      hFull
      h5

  have hConstruction :
      EmergentBiconditional
        C₁
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits
        ↔
      EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) :=

    FBF_biconditionality_invariant
      Corr.constructionIso
      R.emergence.baseBits
      R.emergence.roots.bits

  intro hTarget

  apply hReferenceImpossible

  exact
    hConstruction.mpr hTarget


-- --------------------------------------------
-- 24.3 Transfer of the positive
--      degree <= 4 direction
-- --------------------------------------------

theorem PolynomialFBF_degree_le_four_biconditional_transfers
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    (h4 :
      (SplittingPolynomial p).natDegree ≤ 4)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}
    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    EmergentBiconditional
      C₂
      s₂
      (Corr.constructionIso.infoEquiv
        R.emergence.baseBits)
      (Corr.constructionIso.infoEquiv
        R.emergence.roots.bits) := by

  have hReference :
      EmergentBiconditional
        C₁
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits :=

    PolynomialFBF_fullSymmetric_degree_le_four_biconditional
      (E := E)
      R
      C₁
      hFull
      h4
      hConverse
      hComplete

  have hConstruction :
      EmergentBiconditional
        C₁
        R.emergence.entity
        R.emergence.baseBits
        R.emergence.roots.bits
        ↔
      EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) :=

    FBF_biconditionality_invariant
      Corr.constructionIso
      R.emergence.baseBits
      R.emergence.roots.bits

  exact
    hConstruction.mp hReference


-- --------------------------------------------
-- 24.4 Full transferred threshold theorem
-- --------------------------------------------

/-
This is the central Part-24 result.

The target FBF realization need not itself be a
polynomial system.

It only needs to be structurally corresponding
to the polynomial reference realization through:

    FBFStructuralCorrespondence.

Then the threshold criterion transfers:

    target biconditionality
          <->
    reference polynomial degree <= 4.

This is the precise formal meaning of structural
transfer from the Galois reference model.
-/

theorem PolynomialFBF_threshold_four_degree_iff_transfers
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp : Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}
    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)

      ↔

    (SplittingPolynomial p).natDegree ≤ 4 := by

  have hReference :
      EmergentBiconditional
          C₁
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits
        ↔
      (SplittingPolynomial p).natDegree ≤ 4 :=

    PolynomialFBF_fullSymmetric_threshold_four_degree_iff
      (E := E)
      hp
      R
      C₁
      hSound
      hFull
      hConverse
      hComplete

  have hConstruction :
      EmergentBiconditional
          C₁
          R.emergence.entity
          R.emergence.baseBits
          R.emergence.roots.bits
        ↔
      EmergentBiconditional
          C₂
          s₂
          (Corr.constructionIso.infoEquiv
            R.emergence.baseBits)
          (Corr.constructionIso.infoEquiv
            R.emergence.roots.bits) :=

    FBF_biconditionality_invariant
      Corr.constructionIso
      R.emergence.baseBits
      R.emergence.roots.bits

  exact
    hConstruction.symm.trans
      hReference


end
end FBF_Galois


-- ============================================
-- PART 24.5:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 25:
-- BIT-CARDINALITY PRESERVATION AND THE
-- TRANSFERRED TARGET-BIT THRESHOLD
-- ============================================

/-
Part 24 transferred the polynomial threshold theorem
to a structurally corresponding FBF realization:

    target biconditionality
        <->
    reference polynomial degree <= 4.

The remaining step is to express the threshold using
the target system's own semantic symmetry-bit set A₂.

The structural correspondence contains

    symmetryIso.bitEquiv :
      AdjoinedAtom A₁ ≃ AdjoinedAtom A₂.

Since this is an equivalence between the semantic
atoms of A₁ and A₂, their finite cardinalities are
equal:

    |A₁| = |A₂|.

For the polynomial reference system, Part 20 already
proved

    |B_R| = degree(p).

Therefore:

    |A₂| = degree(p).

Combining this with Part 24 yields

    target biconditionality
        <->
    |A₂| <= 4.

This is the target-bit form of the transferred
threshold-4 theorem.
-/


namespace FBF_Galois

noncomputable section


-- --------------------------------------------
-- 25.1 A bit-symmetry isomorphism preserves
--      bit cardinality
-- --------------------------------------------

theorem FBFBitSymmetryIso_bitContent_eq
    {A₁ A₂ : InformationSet}
    {G₁ G₂ : Type v}
    [Group G₁]
    [Group G₂]
    {S₁ : FBFBitSymmetry A₁ G₁}
    {S₂ : FBFBitSymmetry A₂ G₂}
    (I : FBFBitSymmetryIso S₁ S₂) :

    BitContent A₁ =
      BitContent A₂ := by

  have hCard :
      Fintype.card (AdjoinedAtom A₁) =
        Fintype.card (AdjoinedAtom A₂) :=

    Fintype.card_congr
      I.bitEquiv

  simpa
    [BitContent, AdjoinedAtom]
    using hCard


-- --------------------------------------------
-- 25.2 Structural correspondence preserves
--      semantic bit cardinality
-- --------------------------------------------

theorem FBFStructuralCorrespondence_bitContent_eq
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {A₁ A₂ : InformationSet}

    {G₁ G₂ : Type v}
    [Group G₁]
    [Group G₂]

    {S₁ : FBFBitSymmetry A₁ G₁}
    {S₂ : FBFBitSymmetry A₂ G₂}

    {C₁ C₂ : FBFConstructionSystem}

    {s₁ s₂ : FObject}

    (Corr :
      FBFStructuralCorrespondence
        S₁
        S₂
        C₁
        C₂
        s₁
        s₂) :

    BitContent A₁ =
      BitContent A₂ := by

  exact
    FBFBitSymmetryIso_bitContent_eq
      Corr.symmetryIso


-- --------------------------------------------
-- 25.3 Polynomial reference root bits and
--      target symmetry bits have equal size
-- --------------------------------------------

theorem PolynomialFBF_target_bitContent_eq_reference
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    [Field F]

    {p : Polynomial F}

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    BitContent
        R.emergence.roots.bits
      =
    BitContent A₂ := by

  exact
    FBFStructuralCorrespondence_bitContent_eq
      Corr


-- --------------------------------------------
-- 25.4 Target symmetry-bit count equals
--      the reference polynomial degree
-- --------------------------------------------

theorem PolynomialFBF_target_bitContent_eq_degree
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]

    {F : Type u}
    [Field F]

    {p : Polynomial F}

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    BitContent A₂ =
      (SplittingPolynomial p).natDegree := by

  have hCorr :
      BitContent
          R.emergence.roots.bits
        =
      BitContent A₂ :=

    PolynomialFBF_target_bitContent_eq_reference
      R
      C₁
      S₂
      C₂
      s₂
      Corr

  have hReference :
      BitContent
          R.emergence.roots.bits
        =
      (SplittingPolynomial p).natDegree :=

    PolynomialVietaFBF_root_bit_count_eq_degree
      R

  exact
    hCorr.symm.trans
      hReference


-- --------------------------------------------
-- 25.5 Target-bit negative obstruction
-- --------------------------------------------

/-
If the target symmetry-bit set has at least five
semantic bits, its cardinality equals a reference
degree at least five.

Part 24 then transfers the negative obstruction.
-/

theorem PolynomialFBF_target_five_bits_obstruction
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp :
      Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂)

    (h5target :
      5 ≤ BitContent A₂) :

    ¬ EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) := by

  have hCount :
      BitContent A₂ =
        (SplittingPolynomial p).natDegree :=

    PolynomialFBF_target_bitContent_eq_degree
      R
      C₁
      S₂
      C₂
      s₂
      Corr

  have h5degree :
      5 ≤
        (SplittingPolynomial p).natDegree := by

    rw [← hCount]

    exact h5target

  exact
    PolynomialFBF_degree_ge_five_obstruction_transfers
      (E := E)
      hp
      R
      C₁
      hSound
      hFull
      h5degree
      S₂
      C₂
      s₂
      Corr


-- --------------------------------------------
-- 25.6 Target-bit positive direction
-- --------------------------------------------

/-
For at most four target semantic bits, the reference
polynomial degree is also at most four.

The positive result from Part 24 therefore transfers,
under the explicit radical converse/completeness
bridges.
-/

theorem PolynomialFBF_target_at_most_four_bits_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂)

    (h4target :
      BitContent A₂ ≤ 4) :

    EmergentBiconditional
      C₂
      s₂
      (Corr.constructionIso.infoEquiv
        R.emergence.baseBits)
      (Corr.constructionIso.infoEquiv
        R.emergence.roots.bits) := by

  have hCount :
      BitContent A₂ =
        (SplittingPolynomial p).natDegree :=

    PolynomialFBF_target_bitContent_eq_degree
      R
      C₁
      S₂
      C₂
      s₂
      Corr

  have h4degree :
      (SplittingPolynomial p).natDegree ≤ 4 := by

    rw [← hCount]

    exact h4target

  exact
    PolynomialFBF_degree_le_four_biconditional_transfers
      (E := E)
      R
      C₁
      hFull
      h4degree
      hConverse
      hComplete
      S₂
      C₂
      s₂
      Corr


-- ============================================
-- FULL TARGET-BIT THRESHOLD
-- ============================================


-- --------------------------------------------
-- 25.7 Transferred threshold-4 theorem in
--      the target system's bit language
-- --------------------------------------------

theorem PolynomialFBF_threshold_four_target_bits_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp :
      Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hFull :
      FullSymmetricGaloisOnVietaDegree p)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂) :

    EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)

      ↔

    BitContent A₂ ≤ 4 := by

  have hDegree :
      EmergentBiconditional
          C₂
          s₂
          (Corr.constructionIso.infoEquiv
            R.emergence.baseBits)
          (Corr.constructionIso.infoEquiv
            R.emergence.roots.bits)
        ↔
      (SplittingPolynomial p).natDegree ≤ 4 :=

    PolynomialFBF_threshold_four_degree_iff_transfers
      (E := E)
      hp
      R
      C₁
      hSound
      hFull
      hConverse
      hComplete
      S₂
      C₂
      s₂
      Corr

  have hCount :
      BitContent A₂ =
        (SplittingPolynomial p).natDegree :=

    PolynomialFBF_target_bitContent_eq_degree
      R
      C₁
      S₂
      C₂
      s₂
      Corr

  rw [hCount]

  exact hDegree


end
end FBF_Galois


-- ============================================
-- PART 25.8:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 26:
-- COMMUTABLE-BLOCK DECOMPOSITION AND THE
-- GENERALIZED THRESHOLD-4 THEOREM
-- ============================================

/-
The previous threshold theorem treated a single
commutable block:

    A = {b₁, ..., bₙ}

with governing symmetry

    Sₙ.

In a general FBF construction, however, independent
adjoined bits may arise in successive commutable
blocks.

Example:

    6 independent bits = 2 + 2 + 2

may have symmetry

    S₂ × S₂ × S₂

rather than S₆.

Therefore the relevant threshold is NOT the total
number of independent adjoined bits.

The correct criterion is:

    every simultaneously commutable block
    has size at most four.

For a block profile

    [n₁, n₂, ..., nₖ]

the governing symmetry is represented below by

    S_n₁ × S_n₂ × ... × S_nₖ.

Part 26 proves:

    block symmetry solvable
        ↔
    every block size <= 4.

Combining this with the Part-21
solvability/biconditionality criterion yields

    FBF biconditional
        ↔
    every commutable block has size <= 4.
-/


namespace FBF_Galois


-- --------------------------------------------
-- 26.1 Finite product of block symmetries
-- --------------------------------------------

/-
A list

    [n₁, n₂, ..., nₖ]

records the sizes of successive independent
commutable blocks.

The corresponding group is recursively

    []            -> trivial group
    n :: ns       -> Sₙ × BlockSymmetryGroup ns.
-/

def BlockSymmetryGroup :
    List ℕ → Type

  | [] =>
      Unit

  | n :: ns =>
      SymmetricGroupAt n ×
        BlockSymmetryGroup ns


-- --------------------------------------------
-- 26.2 Group structure on the block product
-- --------------------------------------------

instance blockSymmetryGroupGroup
    (sizes : List ℕ) :
    Group (BlockSymmetryGroup sizes) := by

  induction sizes with

  | nil =>
      change Group Unit
      infer_instance

  | cons n ns ih =>

      change
        Group
          (SymmetricGroupAt n ×
            BlockSymmetryGroup ns)

      letI :
          Group (BlockSymmetryGroup ns) :=
        ih

      infer_instance


-- --------------------------------------------
-- 26.3 If every block has size <= 4,
--      the whole block symmetry is solvable
-- --------------------------------------------

theorem BlockSymmetryGroup_solvable_of_all_le_four
    (sizes : List ℕ)
    (hSmall :
      ∀ n,
        n ∈ sizes →
        n ≤ 4) :

    Group.IsSolvable
      (BlockSymmetryGroup sizes) := by

  induction sizes with

  | nil =>

      change
        Group.IsSolvable Unit

      infer_instance

  | cons n ns ih =>

      have hn :
          n ≤ 4 := by

        exact
          hSmall n
            (by simp)

      have hTailSmall :
          ∀ m,
            m ∈ ns →
            m ≤ 4 := by

        intro m hm

        exact
          hSmall m
            (by
              simp [hm])

      have hHead :
          Group.IsSolvable
            (SymmetricGroupAt n) :=

        symmetricGroup_solvable_of_le_four
          hn

      have hTail :
          Group.IsSolvable
            (BlockSymmetryGroup ns) :=

        ih hTailSmall

      letI :
          Group.IsSolvable
            (SymmetricGroupAt n) :=
        hHead

      letI :
          Group.IsSolvable
            (BlockSymmetryGroup ns) :=
        hTail

      change
        Group.IsSolvable
          (SymmetricGroupAt n ×
            BlockSymmetryGroup ns)

      infer_instance


-- --------------------------------------------
-- 26.4 A solvable block product forces
--      every block to have size <= 4
-- --------------------------------------------

theorem all_le_four_of_BlockSymmetryGroup_solvable
    (sizes : List ℕ)
    (hSolv :
      Group.IsSolvable
        (BlockSymmetryGroup sizes)) :

    ∀ n,
      n ∈ sizes →
      n ≤ 4 := by

  induction sizes with

  | nil =>

      intro n hn

      simp at hn

  | cons n ns ih =>

      have hProd :
          Group.IsSolvable
            (SymmetricGroupAt n ×
              BlockSymmetryGroup ns) := by

        simpa [BlockSymmetryGroup]
          using hSolv

      have hHead :
          Group.IsSolvable
            (SymmetricGroupAt n) := by

        exact
          @Group.isSolvable_of_surjective
            (SymmetricGroupAt n ×
              BlockSymmetryGroup ns)
            (SymmetricGroupAt n)
            inferInstance
            inferInstance
            (MonoidHom.fst
              (SymmetricGroupAt n)
              (BlockSymmetryGroup ns))
            (by
              intro x
              refine ⟨(x, 1), ?_⟩
              rfl)
            hProd

      have hTail :
          Group.IsSolvable
            (BlockSymmetryGroup ns) := by

        exact
          @Group.isSolvable_of_surjective
            (SymmetricGroupAt n ×
              BlockSymmetryGroup ns)
            (BlockSymmetryGroup ns)
            inferInstance
            inferInstance
            (MonoidHom.snd
              (SymmetricGroupAt n)
              (BlockSymmetryGroup ns))
            (by
              intro x
              refine ⟨(1, x), ?_⟩
              rfl)
            hProd

      have hn4 :
          n ≤ 4 := by

        by_contra hNot

        have h5 :
            5 ≤ n := by
          omega

        exact
          (symmetricGroup_not_solvable_of_five_le
            h5)
            hHead

      have hTail4 :
          ∀ m,
            m ∈ ns →
            m ≤ 4 :=

        ih hTail

      intro m hm

      rcases List.mem_cons.mp hm with
        hmn | hmTail

      · subst m
        exact hn4

      · exact
          hTail4 m hmTail


-- --------------------------------------------
-- 26.5 Exact solvability criterion for
--      a block decomposition
-- --------------------------------------------

theorem BlockSymmetryGroup_solvable_iff
    (sizes : List ℕ) :

    Group.IsSolvable
        (BlockSymmetryGroup sizes)

      ↔

    ∀ n,
      n ∈ sizes →
      n ≤ 4 := by

  constructor

  · intro hSolv

    exact
      all_le_four_of_BlockSymmetryGroup_solvable
        sizes
        hSolv

  · intro hSmall

    exact
      BlockSymmetryGroup_solvable_of_all_le_four
        sizes
        hSmall


-- --------------------------------------------
-- 26.6 A general FBF group may realize the
--      block symmetry only up to isomorphism
-- --------------------------------------------

def FullBlockSymmetryAt
    (G : Type*)
    [Group G]
    (sizes : List ℕ) : Prop :=

  Nonempty
    (G ≃*
      BlockSymmetryGroup sizes)


-- --------------------------------------------
-- 26.7 Solvability is preserved by the
--      block-symmetry realization
-- --------------------------------------------

theorem FullBlockSymmetryAt_solvable_iff
    {G : Type*}
    [Group G]
    {sizes : List ℕ}
    (hBlock :
      FullBlockSymmetryAt G sizes) :

    Group.IsSolvable G
      ↔
    Group.IsSolvable
      (BlockSymmetryGroup sizes) := by

  rcases hBlock with
    ⟨e⟩

  constructor

  · intro hG

    exact
      @Group.isSolvable_of_surjective
        G
        (BlockSymmetryGroup sizes)
        inferInstance
        inferInstance
        e.toMonoidHom
        e.surjective
        hG

  · intro hBlocks

    exact
      @Group.isSolvable_of_surjective
        (BlockSymmetryGroup sizes)
        G
        inferInstance
        inferInstance
        e.symm.toMonoidHom
        e.symm.surjective
        hBlocks


-- --------------------------------------------
-- 26.8 General block threshold for solvability
-- --------------------------------------------

theorem FullBlockSymmetryAt_solvable_iff_all_le_four
    {G : Type*}
    [Group G]
    {sizes : List ℕ}
    (hBlock :
      FullBlockSymmetryAt G sizes) :

    Group.IsSolvable G
      ↔
    ∀ n,
      n ∈ sizes →
      n ≤ 4 := by

  exact
    (FullBlockSymmetryAt_solvable_iff
      hBlock).trans
      (BlockSymmetryGroup_solvable_iff
        sizes)


-- ============================================
-- GENERAL FBF BLOCK THRESHOLD
-- ============================================


-- --------------------------------------------
-- 26.9 General threshold theorem
-- --------------------------------------------

/-
This theorem no longer says that the TOTAL number
of adjoined bits must be <= 4.

Instead:

    EmergentBiconditional
        <->
    every commutable block has size <= 4.

The bridge between group solvability and FBF
biconditionality is the criterion already defined
and formalized in Parts 15 and 21.
-/

theorem FBF_block_threshold_four_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C : FBFConstructionSystem)

    (s : FObject)

    (B A : InformationSet)

    (sizes : List ℕ)

    (hBlock :
      FullBlockSymmetryAt
        G
        sizes)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A) :

    EmergentBiconditional
        C
        s
        B
        A

      ↔

    ∀ n,
      n ∈ sizes →
      n ≤ 4 := by

  have hSolv :
      Group.IsSolvable G
        ↔
      ∀ n,
        n ∈ sizes →
        n ≤ 4 :=

    FullBlockSymmetryAt_solvable_iff_all_le_four
      hBlock

  exact
    hCriterion.symm.trans
      hSolv


-- --------------------------------------------
-- 26.10 Negative form:
--       one block of size >= 5 obstructs
--       biconditionality
-- --------------------------------------------

theorem FBF_not_biconditional_of_large_block
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C : FBFConstructionSystem)

    (s : FObject)

    (B A : InformationSet)

    (sizes : List ℕ)

    (hBlock :
      FullBlockSymmetryAt
        G
        sizes)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A)

    (hLarge :
      ∃ n,
        n ∈ sizes ∧
        5 ≤ n) :

    ¬ EmergentBiconditional
        C
        s
        B
        A := by

  intro hBicond

  have hSmall :
      ∀ n,
        n ∈ sizes →
        n ≤ 4 :=

    (FBF_block_threshold_four_iff
      C s B A sizes
      hBlock
      hCriterion).mp
      hBicond

  rcases hLarge with
    ⟨n, hnMem, h5⟩

  have hn4 :
      n ≤ 4 :=
    hSmall n hnMem

  omega


-- --------------------------------------------
-- 26.11 Positive form:
--       arbitrarily many total bits are allowed
--       provided each commutable block <= 4
-- --------------------------------------------

theorem FBF_biconditional_of_all_blocks_le_four
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C : FBFConstructionSystem)

    (s : FObject)

    (B A : InformationSet)

    (sizes : List ℕ)

    (hBlock :
      FullBlockSymmetryAt
        G
        sizes)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A)

    (hSmall :
      ∀ n,
        n ∈ sizes →
        n ≤ 4) :

    EmergentBiconditional
      C
      s
      B
      A := by

  exact
    (FBF_block_threshold_four_iff
      C s B A sizes
      hBlock
      hCriterion).mpr
      hSmall


-- ============================================
-- TRANSFER FROM THE POLYNOMIAL REFERENCE MODEL
-- ============================================


-- --------------------------------------------
-- 26.12 Polynomial-reference criterion
--       transferred to a block-structured target
-- --------------------------------------------

theorem PolynomialFBF_block_threshold_four_transfers
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp :
      Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry A₂ G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂)

    (sizes : List ℕ)

    (hBlocks :
      FullBlockSymmetryAt
        G₂
        sizes) :

    EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)

      ↔

    ∀ n,
      n ∈ sizes →
      n ≤ 4 := by

  have hCriterion :
      SolvabilityBiconditionalCriterion
        G₂
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) :=

    PolynomialFBF_reference_criterion_transfers
      (E := E)
      hp
      R
      C₁
      hSound
      hConverse
      hComplete
      S₂
      C₂
      s₂
      Corr

  exact
    FBF_block_threshold_four_iff
      C₂
      s₂
      (Corr.constructionIso.infoEquiv
        R.emergence.baseBits)
      (Corr.constructionIso.infoEquiv
        R.emergence.roots.bits)
      sizes
      hBlocks
      hCriterion


-- ============================================
-- EXAMPLES
-- ============================================


-- --------------------------------------------
-- 26.13 Six bits in three 2-bit blocks
-- --------------------------------------------

example :
    Group.IsSolvable
      (BlockSymmetryGroup [2, 2, 2]) := by

  apply
    BlockSymmetryGroup_solvable_of_all_le_four

  intro n hn

  simp at hn

  omega


-- --------------------------------------------
-- 26.14 A 2-bit block followed by a 5-bit block
--       is not solvable
-- --------------------------------------------

example :
    ¬ Group.IsSolvable
        (BlockSymmetryGroup [2, 5]) := by

  intro hSolv

  have hSmall :
      ∀ n,
        n ∈ [2, 5] →
        n ≤ 4 :=

    all_le_four_of_BlockSymmetryGroup_solvable
      [2, 5]
      hSolv

  have hFive :
      (5 : ℕ) ≤ 4 :=

    hSmall 5
      (by simp)

  omega


end FBF_Galois


-- ============================================
-- PART 26.15:
-- BASIC CHECKS
-- ============================================

-- ============================================
-- PART 27:
-- ACTUAL FBF COMMUTABLE-BLOCK DECOMPOSITION
-- AND FINAL THRESHOLD-4 THEOREM
-- ============================================

/-
Part 26 proved the abstract block criterion:

    BlockSymmetryGroup [n₁,...,nₖ] is solvable
        ↔
    every nᵢ <= 4.

Part 27 now ties those block sizes directly to the
ACTUAL independent adjoined bits of an FBF
construction.

A block decomposition of A consists of actual
InformationSets

    A₁, A₂, ..., Aₖ

such that:

  1. their union is exactly A;

  2. they are pairwise disjoint;

  3. every block is nonempty;

  4. the blocks consist of independent bits;

  5. each block Aᵢ admits the imposed full
     symmetric S_|Aᵢ| action;

  6. the governing symmetry of the complete
     construction is the product

       S_|A₁| × ... × S_|Aₖ|.

This prevents an artificial decomposition of an
S₅-symmetric block into smaller blocks: the claimed
decomposition must reproduce the actual governing
symmetry group.

The final result is therefore:

    EmergentBiconditional
        ↔
    every actual commutable independent block
    has at most four bits.
-/


namespace FBF_Galois

noncomputable section


-- --------------------------------------------
-- 27.1 Fully commutable / fully symmetric block
-- --------------------------------------------

/-
This is the imposed FBF--Galois correspondence
condition for one block.

A block X of n = |X| semantic bits is declared
fully commutable when the full symmetric group

    S_n

acts faithfully on its semantic atoms.
-/

def FBFFullyCommutableBlock
    (X : InformationSet) : Prop :=

  Nonempty
    (FBFBitSymmetry
      X
      (SymmetricGroupAt
        (BitContent X)))


-- --------------------------------------------
-- 27.2 Actual decomposition of an FBF
--      determining adjoined-bit set
-- --------------------------------------------

structure FBFAdjoinedBlockDecomposition
    [InformationStructure]
    [BitDependency]

    (B A : InformationSet)
    (s : FObject)

    (G : Type*)
    [Group G] where

  -- A really is a minimal determining
  -- independent adjoined-bit set.
  determining :
    DeterminingAdjoinedBits
      B A s

  -- Actual subsets of A representing the
  -- successive commutable blocks.
  blocks :
    List InformationSet

  -- Their union is exactly the complete
  -- adjoined-bit set A.
  cover :
    blocks.foldr
      (fun X Y => X ∪ Y)
      ∅
      =
    A

  -- Distinct blocks contain no common bit.
  pairwiseDisjoint :
    blocks.Pairwise
      (fun X Y =>
        Disjoint X Y)

  -- Empty blocks are excluded.
  blocksNonempty :
    ∀ X,
      X ∈ blocks →
      X ≠ ∅

  -- Every block is itself composed of
  -- independent semantic bits.
  blockIndependent :
    ∀ X,
      X ∈ blocks →
      IndependentSet X

  -- Each block carries its full S_n symmetry.
  blockCommutable :
    ∀ X,
      X ∈ blocks →
      FBFFullyCommutableBlock X

  -- The actual governing group of the whole
  -- construction is the product of the
  -- symmetric groups belonging to the blocks.
  governingSymmetry :
    FullBlockSymmetryAt
      G
      (blocks.map BitContent)


-- --------------------------------------------
-- 27.3 Such a decomposition really concerns
--      adjoined bits
-- --------------------------------------------

theorem FBFAdjoinedBlockDecomposition_adjoinedBits
    [InformationStructure]
    [BitDependency]

    {B A : InformationSet}
    {s : FObject}

    {G : Type*}
    [Group G]

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G) :

    AdjoinedBits B A := by

  exact
    determiningAdjoinedBits_implies_adjoinedBits
      D.determining


-- --------------------------------------------
-- 27.4 Actual block sizes
-- --------------------------------------------

def FBFAdjoinedBlockDecomposition.blockSizes
    [InformationStructure]
    [BitDependency]

    {B A : InformationSet}
    {s : FObject}

    {G : Type*}
    [Group G]

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G) :

    List ℕ :=

  D.blocks.map BitContent


-- --------------------------------------------
-- 27.5 Governing symmetry is exactly the
--      block-product symmetry
-- --------------------------------------------

theorem FBFAdjoinedBlockDecomposition_fullBlockSymmetry
    [InformationStructure]
    [BitDependency]

    {B A : InformationSet}
    {s : FObject}

    {G : Type*}
    [Group G]

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G) :

    FullBlockSymmetryAt
      G
      D.blockSizes := by

  exact
    D.governingSymmetry


-- --------------------------------------------
-- 27.6 FINAL GENERAL FBF BLOCK THRESHOLD
-- --------------------------------------------

/-
This theorem refers to the ACTUAL blocks of A,
not merely to an externally supplied list of
numbers.

It says:

    FBF biconditionality
        ↔
    every actual commutable block X has
    |X| <= 4.
-/

theorem FBF_actual_block_threshold_four_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C :
      FBFConstructionSystem)

    (s :
      FObject)

    (B A :
      InformationSet)

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A) :

    EmergentBiconditional
        C
        s
        B
        A

      ↔

    ∀ X,
      X ∈ D.blocks →
      BitContent X ≤ 4 := by

  have hAbstract :
      EmergentBiconditional
          C
          s
          B
          A
        ↔
      ∀ n,
        n ∈ D.blockSizes →
        n ≤ 4 :=

    FBF_block_threshold_four_iff
      C
      s
      B
      A
      D.blockSizes
      D.governingSymmetry
      hCriterion

  constructor

  · intro hBicond

    have hSmall :
        ∀ n,
          n ∈ D.blockSizes →
          n ≤ 4 :=

      hAbstract.mp hBicond

    intro X hX

    apply
      hSmall
        (BitContent X)

    exact
      List.mem_map.mpr
        ⟨X, hX, rfl⟩

  · intro hBlocks

    apply
      hAbstract.mpr

    intro n hn

    rcases
      List.mem_map.mp hn
      with
      ⟨X, hX, rfl⟩

    exact
      hBlocks X hX


-- --------------------------------------------
-- 27.7 Negative formulation:
--      one actual block of five or more bits
--      destroys biconditionality
-- --------------------------------------------

theorem FBF_actual_large_block_not_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C :
      FBFConstructionSystem)

    (s :
      FObject)

    (B A :
      InformationSet)

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A)

    (hLarge :
      ∃ X,
        X ∈ D.blocks
          ∧
        5 ≤ BitContent X) :

    ¬ EmergentBiconditional
        C
        s
        B
        A := by

  intro hBicond

  have hSmall :
      ∀ X,
        X ∈ D.blocks →
        BitContent X ≤ 4 :=

    (FBF_actual_block_threshold_four_iff
      C
      s
      B
      A
      D
      hCriterion).mp
      hBicond

  rcases hLarge with
    ⟨X, hX, h5⟩

  have h4 :
      BitContent X ≤ 4 :=

    hSmall X hX

  omega


-- --------------------------------------------
-- 27.8 Positive formulation:
--      arbitrarily many total bits are allowed
--      when every actual commutable block <= 4
-- --------------------------------------------

theorem FBF_actual_blocks_le_four_biconditional
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C :
      FBFConstructionSystem)

    (s :
      FObject)

    (B A :
      InformationSet)

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A)

    (hSmall :
      ∀ X,
        X ∈ D.blocks →
        BitContent X ≤ 4) :

    EmergentBiconditional
      C
      s
      B
      A := by

  exact
    (FBF_actual_block_threshold_four_iff
      C
      s
      B
      A
      D
      hCriterion).mpr
      hSmall


-- --------------------------------------------
-- 27.9 Necessary condition:
--      biconditionality forces every actual
--      commutable block to have at most 4 bits
-- --------------------------------------------

theorem FBF_biconditional_implies_actual_blocks_le_four
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {G : Type*}
    [Group G]

    (C :
      FBFConstructionSystem)

    (s :
      FObject)

    (B A :
      InformationSet)

    (D :
      FBFAdjoinedBlockDecomposition
        B A s G)

    (hCriterion :
      SolvabilityBiconditionalCriterion
        G
        C
        s
        B
        A)

    (hBicond :
      EmergentBiconditional
        C
        s
        B
        A) :

    ∀ X,
      X ∈ D.blocks →
      BitContent X ≤ 4 := by

  exact
    (FBF_actual_block_threshold_four_iff
      C
      s
      B
      A
      D
      hCriterion).mp
      hBicond


-- ============================================
-- FINAL TRANSFER FROM THE POLYNOMIAL/GALOIS
-- REFERENCE REALIZATION
-- ============================================


-- --------------------------------------------
-- 27.10 Final FBF--Galois block theorem
-- --------------------------------------------

/-
Here the actual target adjoined set is

    Corr.constructionIso.infoEquiv
      R.emergence.roots.bits.

The decomposition D therefore acts directly on
the target construction's own adjoined bits.

No identification with an abstract numerical
profile is required: the profile is extracted
from D.blocks itself.
-/

theorem PolynomialFBF_final_block_threshold_four_iff
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp :
      Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry
        A₂
        G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂)

    (D :
      FBFAdjoinedBlockDecomposition
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)
        s₂
        G₂) :

    EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)

      ↔

    ∀ X,
      X ∈ D.blocks →
      BitContent X ≤ 4 := by

  have hCriterion :
      SolvabilityBiconditionalCriterion
        G₂
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) :=

    PolynomialFBF_reference_criterion_transfers
      (E := E)
      hp
      R
      C₁
      hSound
      hConverse
      hComplete
      S₂
      C₂
      s₂
      Corr

  exact
    FBF_actual_block_threshold_four_iff
      C₂
      s₂
      (Corr.constructionIso.infoEquiv
        R.emergence.baseBits)
      (Corr.constructionIso.infoEquiv
        R.emergence.roots.bits)
      D
      hCriterion


-- --------------------------------------------
-- 27.11 Final negative form
-- --------------------------------------------

theorem PolynomialFBF_final_large_block_obstruction
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]

    {F : Type u}
    {E : Type*}

    [Field F]
    [Field E]
    [Algebra F E]

    {p : Polynomial F}

    (hp :
      Irreducible p)

    (R :
      PolynomialVietaFBFRealization p)

    (C₁ :
      FBFConstructionSystem)

    (hSound :
      PolynomialFBFRadicalSoundness
        (E := E)
        R C₁)

    (hConverse :
      GaloisRadicalConverseAt
        (E := E)
        p)

    (hComplete :
      PolynomialFBFRadicalCompleteness
        (E := E)
        R C₁)

    {A₂ : InformationSet}

    {G₂ : Type u}
    [Group G₂]

    (S₂ :
      FBFBitSymmetry
        A₂
        G₂)

    (C₂ :
      FBFConstructionSystem)

    (s₂ :
      FObject)

    (Corr :
      FBFStructuralCorrespondence
        (PolynomialFBFBitSymmetry
          R.emergence.roots)
        S₂
        C₁
        C₂
        R.emergence.entity
        s₂)

    (D :
      FBFAdjoinedBlockDecomposition
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits)
        s₂
        G₂)

    (hLarge :
      ∃ X,
        X ∈ D.blocks
          ∧
        5 ≤ BitContent X) :

    ¬ EmergentBiconditional
        C₂
        s₂
        (Corr.constructionIso.infoEquiv
          R.emergence.baseBits)
        (Corr.constructionIso.infoEquiv
          R.emergence.roots.bits) := by

  intro hBicond

  have hFinal :=
    PolynomialFBF_final_block_threshold_four_iff
      (E := E)
      hp
      R
      C₁
      hSound
      hConverse
      hComplete
      S₂
      C₂
      s₂
      Corr
      D

  have hSmall :
      ∀ X,
        X ∈ D.blocks →
        BitContent X ≤ 4 :=

    hFinal.mp hBicond

  rcases hLarge with
    ⟨X, hX, h5⟩

  have h4 :
      BitContent X ≤ 4 :=
    hSmall X hX

  omega


end
end FBF_Galois


-- ============================================
-- PART 27.12:
-- BASIC CHECKS
-- ============================================

#print axioms FBF_Galois.FBF_actual_block_threshold_four_iff
#print axioms FBF_Galois.PolynomialFBF_final_block_threshold_four_iff
#print axioms FBF_Galois.PolynomialFBF_final_large_block_obstruction
