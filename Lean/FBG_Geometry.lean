import FBF_Core

-- ============================================
-- PART 5: GEOMETRIC PRIMITIVES
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

def triangleFObject (_t : Triangle) : FObject :=
  { Obj := Triangle }

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

#check Point
#check Line
#check Segment
#check Triangle
#check triangleFObject
#check GeomBit
#check geomToBit
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
