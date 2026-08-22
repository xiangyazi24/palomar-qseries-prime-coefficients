import Mathlib

/-!
# Public coefficient and certificate surface

This Solution-side module contains the fixed mathematical definitions used in
the compared statements.  Palomar forbids project-local imports in the
Challenge closure, so `Challenge.lean` contains a byte-for-byte duplicate of
the marked definition block below.  Comparator checks the resulting exported
declarations, and the repository validator separately checks textual drift.
-/

namespace PalomarQseriesPrimeCoefficients

noncomputable section

/-! ## BEGIN PUBLIC STATEMENT DEFINITIONS -/

/-! ## The coefficient sequence -/

/-- The triangular number `r(r+1)/2`. -/
def triZ (r : Int) : Int := r * (r + 1) / 2

/-- The exponent on an atom coordinate. -/
def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

/-- The integral parity sign. -/
def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Positive-cone coefficient. -/
def ACoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => -negOnePowInt (↑p.2))

/-- Negative-cone coefficient in translated natural coordinates. -/
def DCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => negOnePowInt (-(↑p.2 + 1)))

/-- Difference of the two norm-theta cones. -/
def BCoeff (N : Nat) : Int := DCoeff N + ACoeff N

/-! ## Golden integers and the geometric sector invariant -/

/-- An element `a + b phi` of the golden integer lattice. -/
@[ext]
structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

instance : Zero PhiInt := ⟨⟨0, 0⟩⟩
instance : One PhiInt := ⟨⟨1, 0⟩⟩
instance : Add PhiInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg PhiInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub PhiInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul PhiInt :=
  ⟨fun x y =>
    ⟨x.a * y.a + x.b * y.b,
     x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

/-- The algebraic norm in the basis `1, phi`. -/
def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

/-- Galois conjugation. -/
def star (x : PhiInt) : PhiInt := ⟨x.a + x.b, -x.b⟩

/-- The norm-one fundamental unit `1 + phi`. -/
def eps : PhiInt := ⟨1, 1⟩

end PhiInt

/-- Reduction of a golden integer modulo two. -/
def toF4 (x : PhiInt) : ZMod 2 × ZMod 2 :=
  (↑x.a, ↑x.b)

/-- A label for the three nonzero residue classes modulo two. -/
def discreteLog (x : ZMod 2 × ZMod 2) : ZMod 3 :=
  if x = (1, 0) then 0
  else if x = (1, 1) then 1
  else if x = (0, 1) then 2
  else 0

/-- The residue label induced by an integral sector lift. -/
structure SectorCert (x : PhiInt) where
  δ : ZMod 3

/-- The finite residue-class logarithm of a golden integer modulo two. -/
def lambdaOf (x : PhiInt) : ZMod 3 := discreteLog (toF4 x)

/-- The sector-minus-residue class in `ZMod 3` governing prime magnitude. -/
def iotaCert (x : PhiInt) (c : SectorCert x) : ZMod 3 :=
  c.δ - lambdaOf x

/-! The next definitions are the integral, not real-analytic, formulation of
the canonical fundamental sector. -/

/-- Twice the first real embedding of `a + b phi`, with denominators cleared. -/
def Tr (x : PhiInt) : Int := 2 * x.a + x.b

/-- A cleared-denominator form of the second fundamental-window coordinate. -/
def windowComp (x : PhiInt) : Int := x.b - 3 * x.a

/-- Multiplication by `eps = 1 + phi` in coordinates. -/
def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2 * x.b⟩

/-- Multiplication by `eps^{-1} = 2 - phi` in coordinates. -/
def epsInvMul (x : PhiInt) : PhiInt :=
  ⟨2 * x.a - x.b, -x.a + x.b⟩

/-- Iterated multiplication by the fundamental unit `eps`. -/
def epsNatMul : Nat → PhiInt → PhiInt
  | 0, x => x
  | n + 1, x => epsMul (epsNatMul n x)

/-- Iterated multiplication by the inverse fundamental unit. -/
def epsInvNatMul : Nat → PhiInt → PhiInt
  | 0, x => x
  | n + 1, x => epsInvMul (epsInvNatMul n x)

/-- The action of the integral power `eps^m`. -/
def epsZPowMul : Int → PhiInt → PhiInt
  | Int.ofNat n, x => epsNatMul n x
  | Int.negSucc n, x => epsInvNatMul (n + 1) x

/-- Association by a signed norm-one unit. -/
def sameIdeal (x y : PhiInt) : Prop :=
  ∃ (m : Int) (negative : Bool),
    y = match negative with
      | false => epsZPowMul m x
      | true => -(epsZPowMul m x)

/-- The two strict fundamental-window coordinates have the same nonzero sign. -/
def SameWindowSign (x : PhiInt) : Prop :=
  (0 < Tr x ∧ 0 < windowComp x) ∨
  (Tr x < 0 ∧ windowComp x < 0)

/-- An actual integral fundamental-window normalization. -/
structure GeometricSectorCert (x : PhiInt) where
  lift : Int
  normalized : SameWindowSign (epsZPowMul (-lift) x)

/-- Forget the geometric inequalities while retaining the lift modulo three. -/
def GeometricSectorCert.toSectorCert {x : PhiInt}
    (c : GeometricSectorCert x) : SectorCert x :=
  ⟨(c.lift : ZMod 3)⟩

/-! ## END PUBLIC STATEMENT DEFINITIONS -/

end
end PalomarQseriesPrimeCoefficients
