import Mathlib

/-!
# Reindexed nonmultiplicativity and unconditional split-prime coefficients

The custom notions needed by the compared theorem statements are defined
directly in this file because Palomar permits only trusted statement-library
sources in the Challenge import closure.  The marked block is duplicated
byte-for-byte in the Solution-side public module and checked for drift.
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

/-- The A-cone contribution to `B_N`, including the outer minus sign. -/
def ACoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => -negOnePowInt (↑p.2))

/-- The D-cone contribution to `B_N` in translated natural coordinates. -/
def DCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => negOnePowInt (-(↑p.2 + 1)))

/-- The manuscript coefficient `B_N`: D-cone sum minus A-cone sum. -/
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

/-- The fundamental totally positive unit `eps = 1 + phi = phi^2`, of norm one. -/
def eps : PhiInt := ⟨1, 1⟩

end PhiInt

/-- Reduction of a golden integer modulo two. -/
def toF4 (x : PhiInt) : ZMod 2 × ZMod 2 :=
  (↑x.a, ↑x.b)

/-- The exponent label of the three nonzero mod-two residue classes;
the zero class is totalized to `0`. -/
def discreteLog (x : ZMod 2 × ZMod 2) : ZMod 3 :=
  if x = (1, 0) then 0
  else if x = (1, 1) then 1
  else if x = (0, 1) then 2
  else 0

/-- A sector residue label in `ZMod 3`, indexed by `x`;
this structure alone does not certify a geometric lift. -/
structure SectorCert (x : PhiInt) where
  δ : ZMod 3

/-- The corresponding totalized mod-two residue label of a golden integer;
on nonzero reduction it is the discrete logarithm to base `eps`. -/
def lambdaOf (x : PhiInt) : ZMod 3 := discreteLog (toF4 x)

/-- The formal sector-minus-residue value `c.δ - lambdaOf x` in `ZMod 3`.
For labels obtained from a geometric certificate at an admissible prime,
the selected theorem relates value `1` to coefficient magnitude `2`. -/
def iotaCert (x : PhiInt) (c : SectorCert x) : ZMod 3 :=
  c.δ - lambdaOf x

/-! The next definitions are the integral, not real-analytic, formulation of
the canonical fundamental sector. -/

/-- The field trace of `a + b phi`, namely `2a + b`. -/
def Tr (x : PhiInt) : Int := 2 * x.a + x.b

/-- The second integral fundamental-window coordinate `b - 3a`. -/
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

/-! ## Registered theorems -/

/-- Closed coefficient inequality underlying the manuscript's reindexed
nonmultiplicativity witness: for `a(M) = B_((M - 1) / 10)`, this is
`a(341) != a(11) * a(31)`. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  sorry

/-- Complete finite classification at every rational prime congruent to one
modulo ten.  The coefficient is one of four signed values; a norm-negative
golden-integer generator exists; and every such generator has a genuine
integral-window certificate for which magnitude two is exactly iota class
one, independently of the chosen certificate. -/
theorem prime_BCoeff_complete_classification
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) ∧
    (∃ x : PhiInt, PhiInt.norm x = -(p : Int)) ∧
    ∀ {x : PhiInt}, PhiInt.norm x = -(p : Int) →
      Nonempty (GeometricSectorCert x) ∧
      ∀ c : GeometricSectorCert x,
        (BCoeff ((p - 1) / 10)).natAbs = 2 ↔
          iotaCert x c.toSectorCert = 1 := by
  sorry

/-- The geometric iota class is independent of both the norm-negative
generator and the geometric certificate inside one signed fundamental-unit
orbit. -/
theorem geometric_iota_eq_of_sameIdeal
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x y : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (hxy : sameIdeal x y)
    (c : GeometricSectorCert x) (d : GeometricSectorCert y) :
    iotaCert y d.toSectorCert = iotaCert x c.toSectorCert := by
  sorry

end
end PalomarQseriesPrimeCoefficients
