import FBF_Core

-- ============================================
-- PART 5: GEOMETRIC PRIMITIVES (FBG_Geometry.lean)
-- ============================================

axiom Point : Type

structure Line where
  p1 : Point
  p2 : Point

structure Segment where
  p1 : Point
  p2 : Point

axiom length : Segment → ℝ

noncomputable def dist (P Q : Point) : ℝ :=
  length { p1 := P, p2 := Q }

axiom angle_of_lines : Line → Line → ℝ

axiom OnLine : Point → Line → Prop

structure Circle where
  center : Point
  radius : ℝ

axiom OnCircle : Point → Circle → Prop

axiom ParallelLines : Line → Line → Prop


-- ============================================
-- PART 6: GEOMETRIC ENTITIES
-- ============================================

structure Triangle where
  A : Point
  B : Point
  C : Point

def triangleFObject (t : Triangle) : FObject :=
  { Obj := Triangle, val := t }

noncomputable def side_lengths (t : Triangle) : ℝ × ℝ × ℝ :=
  (dist t.A t.B, dist t.B t.C, dist t.C t.A)

noncomputable def line_AB (t : Triangle) : Line :=
  { p1 := t.A, p2 := t.B }

noncomputable def line_BC (t : Triangle) : Line :=
  { p1 := t.B, p2 := t.C }

noncomputable def line_CA (t : Triangle) : Line :=
  { p1 := t.C, p2 := t.A }

noncomputable def angles (t : Triangle) : ℝ × ℝ × ℝ :=
  (angle_of_lines (line_AB t) (line_CA t),
   angle_of_lines (line_AB t) (line_BC t),
   angle_of_lines (line_BC t) (line_CA t))


-- ============================================
-- PART 7: FBG GEOMETRIC BITS
-- ============================================

inductive GeomBitType where
  | side : GeomBitType
  | angle : GeomBitType
  | sideness : GeomBitType
  deriving DecidableEq, Repr

structure GeomBit where
  kind : GeomBitType
  label : ℕ
  deriving DecidableEq, Repr

def geomBitCode : GeomBit → ℕ
  | { kind := .side,     label } => 3 * label
  | { kind := .angle,    label } => 3 * label + 1
  | { kind := .sideness, label } => 3 * label + 2

def geomToBit (g : GeomBit) : Bit :=
  { id := geomBitCode g }


-- ============================================
-- BASIC CHECK
-- ============================================


-- ============================================
-- PART 8: TRIANGLE BIT SETS
-- ============================================

def base_bits (_ : Triangle) : InformationSet :=
  { geomToBit { kind := GeomBitType.side, label := 0 } }

def adjoined_bits (_ : Triangle) : InformationSet :=
  { geomToBit { kind := GeomBitType.side, label := 1 },
    geomToBit { kind := GeomBitType.side, label := 2 },
    geomToBit { kind := GeomBitType.sideness, label := 0 } }

def equivalent_bits (_ : Triangle) : InformationSet :=
  { geomToBit { kind := GeomBitType.angle, label := 1 },
    geomToBit { kind := GeomBitType.angle, label := 2 },
    geomToBit { kind := GeomBitType.sideness, label := 0 } }

-- ============================================
-- PART 8A: TRIANGLE BIT SEMANTICS
-- ============================================

noncomputable def triangleSideValue
    (t : Triangle)
    (label : ℕ) : ℝ :=
  match label with
  | 0 => dist t.A t.B
  | 1 => dist t.B t.C
  | 2 => dist t.C t.A
  | _ => 0

noncomputable def triangleAngleValue
    (t : Triangle)
    (label : ℕ) : ℝ :=
  match label with
  | 0 => angle_of_lines (line_AB t) (line_CA t)
  | 1 => angle_of_lines (line_AB t) (line_BC t)
  | 2 => angle_of_lines (line_BC t) (line_CA t)
  | _ => 0    

 -- ============================================
-- TRIANGLE SEMANTIC DATA
-- ============================================

noncomputable def triangleSideData
    (t : Triangle) : ℝ × ℝ × ℝ :=
  (triangleSideValue t 0,
   triangleSideValue t 1,
   triangleSideValue t 2)

noncomputable def triangleAngleData
    (t : Triangle) : ℝ × ℝ × ℝ :=
  (triangleAngleValue t 0,
   triangleAngleValue t 1,
   triangleAngleValue t 2)


theorem triangleSideData_eq_side_lengths
    (t : Triangle) :
    triangleSideData t = side_lengths t := by
  rfl


theorem triangleAngleData_eq_angles
    (t : Triangle) :
    triangleAngleData t = angles t := by
  rfl

 theorem equal_side_lengths_give_equal_side_data
    (t1 t2 : Triangle)
    (h : side_lengths t1 = side_lengths t2) :
    triangleSideData t1 = triangleSideData t2 := by
  calc
    triangleSideData t1 = side_lengths t1 :=
      triangleSideData_eq_side_lengths t1
    _ = side_lengths t2 := h
    _ = triangleSideData t2 :=
      (triangleSideData_eq_side_lengths t2).symm  

 -- ============================================
-- CLASSICAL SSS: ORIENTATION-FREE TRIANGLE SHAPE
-- ============================================

noncomputable def triangleShapeFObject
    (t : Triangle) : FObject :=
  {
    Obj := ℝ × ℝ × ℝ
    val := side_lengths t
  }


-- Existing information: one side.
def SSS_base_bits (_ : Triangle) : InformationSet :=
  {
    geomToBit {
      kind := GeomBitType.side,
      label := 0
    }
  }


-- Minimal determining adjoined set for classical SSS:
-- the two remaining side bits.
def SSS_adjoined_bits (_ : Triangle) : InformationSet :=
  {
    geomToBit {
      kind := GeomBitType.side,
      label := 1
    },
    geomToBit {
      kind := GeomBitType.side,
      label := 2
    }
  }


-- Minimal equivalent representation:
-- two independent angle bits.
def SSS_equivalent_bits (_ : Triangle) : InformationSet :=
  {
    geomToBit {
      kind := GeomBitType.angle,
      label := 1
    },
    geomToBit {
      kind := GeomBitType.angle,
      label := 2
    }
  }     


-- ============================================
-- PART 9: TRIANGLE EXPLICIT BIT BALANCE
-- ============================================

theorem triangle_explicit_bit_balance
    (t : Triangle) :
    BitContent (adjoined_bits t) =
    BitContent (equivalent_bits t) := by
  simp [BitContent, adjoined_bits, equivalent_bits,
        geomToBit, geomBitCode]


-- ============================================
-- TRIANGLE: CONCRETE EQUIVALENT-BIT BRIDGE
-- ============================================

def TriangleEquivalentBitsBridge
    [InformationEquivalence]
    [BitDependency]
    (t : Triangle) : Prop :=
  MinimalEquivalentBits
    (triangleFObject t)
    (base_bits t)
    (adjoined_bits t)
    (equivalent_bits t)
theorem triangle_concrete_equivalent_bits
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (t : Triangle)
    (hbridge : TriangleEquivalentBitsBridge t) :
    EquivalentSet
      (triangleFObject t)
      (AdjoinSet (base_bits t) (adjoined_bits t))
      (AdjoinSet (base_bits t) (equivalent_bits t)) := by
  exact hbridge.1
theorem triangle_equivalent_bits_bridge_of
    [InformationEquivalence]
    [BitDependency]
    (t : Triangle)

    (heq :
      EquivalentSet
        (triangleFObject t)
        (AdjoinSet (base_bits t) (adjoined_bits t))
        (AdjoinSet (base_bits t) (equivalent_bits t)))

    (hind :
      IndependentSet (equivalent_bits t))

    (hmin :
      ∀ E' : InformationSet,
        E' ⊆ equivalent_bits t →
        E' ≠ equivalent_bits t →
        ¬ EquivalentSet
          (triangleFObject t)
          (AdjoinSet (base_bits t) (adjoined_bits t))
          (AdjoinSet (base_bits t) E')) :

    TriangleEquivalentBitsBridge t := by
  exact ⟨heq, hind, hmin⟩
-- ============================================
-- TRIANGLE BIT SEMANTICS
-- ============================================

class TriangleBitSemantics
    [InformationStructure]
    (t : Triangle) where

  side_data_realizes :
    InformationStructure.Realizes
      (triangleFObject t)
      (AdjoinSet
        (base_bits t)
        (adjoined_bits t))

  equivalent_data_realizes :
    InformationStructure.Realizes
      (triangleFObject t)
      (AdjoinSet
        (base_bits t)
        (equivalent_bits t))
theorem triangle_side_angle_equivalent
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax1 : FBF_Axiom1_Refined)
    (t : Triangle)
    [TriangleBitSemantics t] :
    EquivalentSet
      (triangleFObject t)
      (AdjoinSet
        (base_bits t)
        (adjoined_bits t))
      (AdjoinSet
        (base_bits t)
        (equivalent_bits t)) := by

  exact ax1.realizations_equivalent
    (triangleFObject t)
    (AdjoinSet
      (base_bits t)
      (adjoined_bits t))
    (AdjoinSet
      (base_bits t)
      (equivalent_bits t))
    (TriangleBitSemantics.side_data_realizes (t := t))
    (TriangleBitSemantics.equivalent_data_realizes (t := t))
-- ============================================
-- TRIANGLE EQUIVALENT-BIT INDEPENDENCE
-- ============================================

class TriangleEquivalentBitIndependence
    [BitDependency]
    (t : Triangle) : Prop where

  independent :
    IndependentSet (equivalent_bits t)


theorem triangle_equivalent_bits_independent
    [BitDependency]
    (t : Triangle)
    [TriangleEquivalentBitIndependence t] :
    IndependentSet (equivalent_bits t) := by
  exact TriangleEquivalentBitIndependence.independent
-- ============================================
-- TRIANGLE EQUIVALENT-BIT MINIMALITY
-- ============================================

class TriangleEquivalentBitMinimality
    [InformationEquivalence]
    (t : Triangle) : Prop where

  minimal :
    ∀ E' : InformationSet,
      E' ⊆ equivalent_bits t →
      E' ≠ equivalent_bits t →
      ¬ EquivalentSet
        (triangleFObject t)
        (AdjoinSet (base_bits t) (adjoined_bits t))
        (AdjoinSet (base_bits t) E')
-- ============================================
-- TRIANGLE EQUIVALENT-BIT BRIDGE DERIVATION
-- ============================================

theorem triangle_equivalent_bits_bridge
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax1 : FBF_Axiom1_Refined)
    (t : Triangle)
    [TriangleBitSemantics t]
    [TriangleEquivalentBitIndependence t]
    [TriangleEquivalentBitMinimality t] :
    TriangleEquivalentBitsBridge t := by

  apply triangle_equivalent_bits_bridge_of t

  · exact triangle_side_angle_equivalent ax1 t

  · exact TriangleEquivalentBitIndependence.independent
      (t := t)

  · exact TriangleEquivalentBitMinimality.minimal
      (t := t)


-- ============================================
-- PART 10: TRIANGLE EMERGENCE FROM REFINED AXIOM 3
-- ============================================

theorem triangle_emergence_from_axiom3
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    [FBF_Axiom3_Refined]
    (t : Triangle)
    (hdet :
      DeterminingAdjoinedBits
        (base_bits t)
        (adjoined_bits t)
        (triangleFObject t)) :
    ∃ E : InformationSet,
      MinimalEquivalentBits
        (triangleFObject t)
        (base_bits t)
        (adjoined_bits t)
        E :=
  FBF_Axiom3_Refined.emergence
    (triangleFObject t)
    (base_bits t)
    (adjoined_bits t)
    hdet

-- ============================================
-- SSS: TOTAL SIDE INFORMATION
-- ============================================

theorem SSS_total_side_bit_count
    (t : Triangle) :
    BitContent
      (AdjoinSet
        (SSS_base_bits t)
        (SSS_adjoined_bits t)) = 3 := by
  simp [BitContent,
        AdjoinSet,
        SSS_base_bits,
        SSS_adjoined_bits,
        geomToBit,
        geomBitCode]


-- ============================================
-- SSS: EXPLICIT BIT BALANCE
-- ============================================

theorem SSS_explicit_bit_balance
    (t : Triangle) :
    BitContent (SSS_adjoined_bits t) =
    BitContent (SSS_equivalent_bits t) := by
  simp [BitContent,
        SSS_adjoined_bits,
        SSS_equivalent_bits,
        geomToBit,
        geomBitCode]


-- ============================================
-- SSS: CONCRETE EQUIVALENT-BIT BRIDGE
-- ============================================

def SSSEquivalentBitsBridge
    [InformationEquivalence]
    [BitDependency]
    (t : Triangle) : Prop :=
  MinimalEquivalentBits
    (triangleShapeFObject t)
    (SSS_base_bits t)
    (SSS_adjoined_bits t)
    (SSS_equivalent_bits t)






-- ============================================
-- SSS: EQUAL SIDES GIVE THE SAME SHAPE OBJECT
-- ============================================

theorem triangleShapeFObject_eq_of_side_lengths_eq
    (t1 t2 : Triangle)
    (h : side_lengths t1 = side_lengths t2) :
    triangleShapeFObject t1 =
    triangleShapeFObject t2 := by
  exact congrArg
    (fun d : ℝ × ℝ × ℝ =>
      ({ Obj := ℝ × ℝ × ℝ, val := d } : FObject))
    h
-- ============================================
-- PART 11: CLASSICAL SSS FROM REFINED AXIOM 3
-- ============================================
-- ============================================
-- SSS SEMANTIC FACTS
-- ============================================

axiom SSS_determining_bits
    [InformationStructure]
    [BitDependency]
    (t : Triangle) :
    DeterminingAdjoinedBits
      (SSS_base_bits t)
      (SSS_adjoined_bits t)
      (triangleShapeFObject t)


axiom SSS_minimal_equivalent_angles
    [InformationEquivalence]
    [BitDependency]
    (t : Triangle) :
    MinimalEquivalentBits
      (triangleShapeFObject t)
      (SSS_base_bits t)
      (SSS_adjoined_bits t)
      (SSS_equivalent_bits t)

theorem SSS_emergence_from_axiom3
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax3 : FBF_Axiom3_Refined)
    (t : Triangle) :
    ∃ E : InformationSet,
      MinimalEquivalentBits
        (triangleShapeFObject t)
        (SSS_base_bits t)
        (SSS_adjoined_bits t)
        E := by
  exact ax3.emergence
    (triangleShapeFObject t)
    (SSS_base_bits t)
    (SSS_adjoined_bits t)
    (SSS_determining_bits t)
-- ============================================
-- SSS: UNIQUENESS OF THE EMERGENT THEOREM
-- ============================================

theorem SSS_emergent_theorem_unique
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax3 : FBF_Axiom3_Refined)
    (t : Triangle) :
    ∃! T : ax3.EmergentTheoremType,
      ∀ E : InformationSet,
        MinimalEquivalentBits
          (triangleShapeFObject t)
          (SSS_base_bits t)
          (SSS_adjoined_bits t)
          E →
        ax3.Relates
          T
          (triangleShapeFObject t)
          (SSS_base_bits t)
          (SSS_adjoined_bits t)
          E := by
  exact ax3.emergent_theorem_unique
    (triangleShapeFObject t)
    (SSS_base_bits t)
    (SSS_adjoined_bits t)
    (SSS_determining_bits t)
-- ============================================
-- SSS: ANGLE INTERPRETATION OF THE EMERGENT THEOREM
-- ============================================

class SSSAngleSemantics
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax3 : FBF_Axiom3_Refined) where

  angleOutput :
    ax3.EmergentTheoremType →
    (ℝ × ℝ × ℝ)

  realized :
    ∀ (t : Triangle)
      (T : ax3.EmergentTheoremType),
      ax3.Relates
        T
        (triangleShapeFObject t)
        (SSS_base_bits t)
        (SSS_adjoined_bits t)
        (SSS_equivalent_bits t) →
      angleOutput T = angles t
-- ============================================
-- SSS: ANGLE EQUALITY FROM REFINED AXIOM 3
-- ============================================

theorem SSS_angle_equality_from_axiom3
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax3 : FBF_Axiom3_Refined)
    (sem : SSSAngleSemantics ax3)
    (t1 t2 : Triangle)
    (hsides : side_lengths t1 = side_lengths t2) :
    angles t1 = angles t2 := by

  have hshape :
      triangleShapeFObject t1 =
      triangleShapeFObject t2 :=
    triangleShapeFObject_eq_of_side_lengths_eq t1 t2 hsides

  obtain ⟨T, hT, _⟩ :=
    SSS_emergent_theorem_unique ax3 t1

  have hrel1 :
      ax3.Relates
        T
        (triangleShapeFObject t1)
        (SSS_base_bits t1)
        (SSS_adjoined_bits t1)
        (SSS_equivalent_bits t1) :=
    hT
      (SSS_equivalent_bits t1)
      (SSS_minimal_equivalent_angles t1)

  have hE2 :=
    SSS_minimal_equivalent_angles t2

  rw [← hshape] at hE2

  have hE2' :
      MinimalEquivalentBits
        (triangleShapeFObject t1)
        (SSS_base_bits t1)
        (SSS_adjoined_bits t1)
        (SSS_equivalent_bits t2) := by
    simpa [SSS_base_bits, SSS_adjoined_bits] using hE2

  have hrel2' :
      ax3.Relates
        T
        (triangleShapeFObject t1)
        (SSS_base_bits t1)
        (SSS_adjoined_bits t1)
        (SSS_equivalent_bits t2) :=
    hT
      (SSS_equivalent_bits t2)
      hE2'

  have hrel2 :
      ax3.Relates
        T
        (triangleShapeFObject t2)
        (SSS_base_bits t2)
        (SSS_adjoined_bits t2)
        (SSS_equivalent_bits t2) := by
    rw [← hshape]
    simpa [SSS_base_bits, SSS_adjoined_bits] using hrel2'

  have ha1 :
      sem.angleOutput T = angles t1 :=
    sem.realized t1 T hrel1

  have ha2 :
      sem.angleOutput T = angles t2 :=
    sem.realized t2 T hrel2

  calc
    angles t1 = sem.angleOutput T := ha1.symm
    _ = angles t2 := ha2
-- ============================================
-- SSS CONGRUENCE FROM REFINED AXIOM 3
-- ============================================


 -- ============================================
-- SSS CONGRUENCE FROM REFINED AXIOM 3
-- ============================================
-- ============================================
-- DEFINITION OF TRIANGLE CONGRUENCE
-- ============================================

def Congruent (t1 t2 : Triangle) : Prop :=
  side_lengths t1 = side_lengths t2 ∧
  angles t1 = angles t2
  
theorem SSS_congruence
    [InformationStructure]
    [BitDependency]
    [InformationEquivalence]
    (ax3 : FBF_Axiom3_Refined)
    (sem : SSSAngleSemantics ax3)
    (t1 t2 : Triangle)
    (hsides : side_lengths t1 = side_lengths t2) :
    Congruent t1 t2 := by

  constructor

  · exact hsides

  · exact
      SSS_angle_equality_from_axiom3
        ax3
        sem
        t1
        t2
        hsides 
      
