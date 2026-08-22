import Mathlib

/-!
# Nonmultiplicativity and conditional prime coefficients

This Mathlib-only Challenge makes the complete finite coefficient and
certificate burden of the two registered results explicit.
-/

namespace PalomarQseriesPrimeCoefficients

noncomputable section

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

/-! ## Finite prime-certificate data -/

/-- An element `a + b phi` of the golden integer lattice. -/
@[ext]
structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

/-- The algebraic norm in the basis `1, phi`. -/
def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

/-- Galois conjugation. -/
def star (x : PhiInt) : PhiInt := ⟨x.a + x.b, -x.b⟩

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

/-- A supplied `ZMod 3` sector label. It has no geometric membership field. -/
structure SectorCert (x : PhiInt) where
  δ : ZMod 3

def lambdaOf (x : PhiInt) : ZMod 3 := discreteLog (toF4 x)

def iotaCert (x : PhiInt) (c : SectorCert x) : ZMod 3 :=
  c.δ - lambdaOf x

def reflectedSectorCert (x : PhiInt) (c : SectorCert x) :
    SectorCert (PhiInt.star x) where
  δ := -c.δ - 1

def Contributes (x : PhiInt) (c : SectorCert x) : Prop :=
  iotaCert x c ≠ 2

/-- Explicit split-prime generator data consumed by the classifier. -/
structure SplitPrimeCert (p : Nat) where
  π : PhiInt
  hp : Nat.Prime p
  hp10 : p % 10 = 1
  hnorm : PhiInt.norm π = (p : Int) ∨ PhiInt.norm π = -(p : Int)
  hmod2 : toF4 π ≠ (0, 0)

def AAtoms (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun q => E (↑q.1) (↑q.2) = ↑N))

def DAtoms (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun q => E (-((↑q.1 : Int) + 1)) (-((↑q.2 : Int) + 1)) = ↑N))

def AAtomWeight (q : Nat × Nat) : Int :=
  -negOnePowInt (↑q.2)

def DAtomWeight (q : Nat × Nat) : Int :=
  negOnePowInt (-((↑q.2 : Int) + 1))

def atomCount (N : Nat) : Nat := (AAtoms N).card + (DAtoms N).card

/--
The finite hypotheses needed to turn the two conjugate prime labels into a
coefficient classification. The record supplies sign coherence, the two-atom
bound, and both contribution-to-existence implications.
-/
structure PrimeAtomCertificate {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) where
  sign : Int
  all_A : ∀ q ∈ AAtoms ((p - 1) / 10), AAtomWeight q = sign
  all_D : ∀ q ∈ DAtoms ((p - 1) / 10), DAtomWeight q = sign
  one_atom_bound : atomCount ((p - 1) / 10) ≤ 2
  atom_of_left_contributes :
    Contributes sp.π c → 0 < atomCount ((p - 1) / 10)
  atom_of_right_contributes :
    Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) →
      0 < atomCount ((p - 1) / 10)

/-! ## Registered theorems -/

/-- A closed nonmultiplicativity witness for the actual coefficient function. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  sorry

/--
Conditional four-valued classification from an explicit split-prime,
sector-label, and finite atom certificate.
-/
theorem prime_coeff_classification {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  sorry

end
end PalomarQseriesPrimeCoefficients
