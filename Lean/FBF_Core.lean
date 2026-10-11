import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

universe u

structure Bit where
  id : ℕ
  deriving DecidableEq, Repr

abbrev InformationSet := Finset Bit

def BitContent (B : InformationSet) : ℕ :=
  B.card

structure FObject where
  Obj : Type u

class InformationStructure where
  Realizes : FObject → InformationSet → Prop

def Specifies
    [InformationStructure]
    (B : InformationSet)
    (s : FObject) : Prop :=
  InformationStructure.Realizes s B ∧
  ∀ s' : FObject,
    InformationStructure.Realizes s' B →
    s' = s

class BitDependency where
  Dependent : Bit → InformationSet → Prop

def Independent
    [BitDependency]
    (b : Bit)
    (B : InformationSet) : Prop :=
  ¬ BitDependency.Dependent b B

def IndependentSet
    [BitDependency]
    (B : InformationSet) : Prop :=
  ∀ b,
    b ∈ B →
    Independent b (B \ {b})

def MinimalBits
    [InformationStructure]
    [BitDependency]
    (B : InformationSet)
    (s : FObject) : Prop :=
  Specifies B s ∧
  IndependentSet B ∧
  ∀ b,
    b ∈ B →
    ¬ Specifies (B \ {b}) s

def Adjoin
    (B : InformationSet)
    (b : Bit) : InformationSet :=
  insert b B

def AdjoinSet
    (B A : InformationSet) : InformationSet :=
  B ∪ A

def AdjoinedBits
    (B A : InformationSet) : Prop :=
  A ∩ B = ∅ ∧
  A ≠ ∅

class InformationEquivalence where
  Equivalent :
    FObject →
    InformationSet →
    InformationSet →
    Prop

def EquivalentSet
    [InformationEquivalence]
    (s : FObject)
    (B₁ B₂ : InformationSet) : Prop :=
  InformationEquivalence.Equivalent s B₁ B₂

def PreservesInformation
    (B₁ B₂ : InformationSet) : Prop :=
  BitContent B₁ = BitContent B₂

def NullOperation
    [InformationEquivalence]
    (s : FObject)
    (B₁ B₂ : InformationSet) : Prop :=
  EquivalentSet s B₁ B₂

class FBF_Axiom1
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence] where

  minimal_representation :
    ∀ (s : FObject),
      ∃ B : InformationSet,
        MinimalBits B s

  equivalent_refl :
    ∀ (s : FObject)
      (B : InformationSet),
      EquivalentSet s B B

  equivalent_symm :
    ∀ (s : FObject)
      (B₁ B₂ : InformationSet),
      EquivalentSet s B₁ B₂ →
      EquivalentSet s B₂ B₁

  equivalent_trans :
    ∀ (s : FObject)
      (B₁ B₂ B₃ : InformationSet),
      EquivalentSet s B₁ B₂ →
      EquivalentSet s B₂ B₃ →
      EquivalentSet s B₁ B₃

  null_preserves_content :
    ∀ (s : FObject)
      (B₁ B₂ : InformationSet),
      NullOperation s B₁ B₂ →
      BitContent B₁ = BitContent B₂

class FBF_Axiom1_Refined
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    extends FBF_Axiom1 where

  equivalent_preserves_content :
    ∀ (s : FObject)
      (B₁ B₂ : InformationSet),
      EquivalentSet s B₁ B₂ →
      PreservesInformation B₁ B₂

  minimal_representations_equivalent :
    ∀ (s : FObject)
      (B₁ B₂ : InformationSet),
      MinimalBits B₁ s →
      MinimalBits B₂ s →
      EquivalentSet s B₁ B₂

  realizations_equivalent :
    ∀ (s : FObject)
      (B₁ B₂ : InformationSet),
      InformationStructure.Realizes s B₁ →
      InformationStructure.Realizes s B₂ →
      EquivalentSet s B₁ B₂

class FBF_Axiom3
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence] where

  emergence :
    ∀ (s : FObject)
      (B A : InformationSet),
      MinimalBits B s →
      AdjoinedBits B A →
      ∃! (E : InformationSet),
        E ≠ B ∧
        EquivalentSet s (AdjoinSet B A) E

  adjoined_count : ℕ

  equivalent_count : ℕ

  count_eq :
    adjoined_count = equivalent_count

#check FBF_Axiom1
#check FBF_Axiom1_Refined
#check FBF_Axiom3
