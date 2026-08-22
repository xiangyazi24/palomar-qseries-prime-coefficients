import PalomarQseriesPrimeCoefficients

/-!
# Nonmultiplicativity and conditional prime coefficients

This file repeats the public statement surface, converts its certificate
records explicitly to the extracted internal types, and applies the two
verified internal endpoints.
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

/-! ## Explicit public-to-internal transport -/

private def toInternalPhi (x : PhiInt) :
    QseriesFormalization.Ch10.PhiInt :=
  ⟨x.a, x.b⟩

private theorem BCoeff_eq_internal (N : Nat) :
    BCoeff N = QseriesFormalization.Ch10.BCoeff N := by
  rfl

private theorem AAtoms_eq_internal (N : Nat) :
    AAtoms N = QseriesFormalization.Ch10.AAtoms N := by
  rfl

private theorem DAtoms_eq_internal (N : Nat) :
    DAtoms N = QseriesFormalization.Ch10.DAtoms N := by
  rfl

private theorem AAtomWeight_eq_internal (q : Nat × Nat) :
    AAtomWeight q = QseriesFormalization.Ch10.AAtomWeight q := by
  rfl

private theorem DAtomWeight_eq_internal (q : Nat × Nat) :
    DAtomWeight q = QseriesFormalization.Ch10.DAtomWeight q := by
  rfl

private theorem atomCount_eq_internal (N : Nat) :
    atomCount N = QseriesFormalization.Ch10.atomCount N := by
  rfl

private def toInternalSector {x : PhiInt} (c : SectorCert x) :
    QseriesFormalization.Ch10.SectorCert (toInternalPhi x) where
  δ := c.δ

private theorem contributes_iff_internal (x : PhiInt) (c : SectorCert x) :
    Contributes x c ↔
      QseriesFormalization.Ch10.Contributes
        (toInternalPhi x) (toInternalSector c) := by
  rfl

private theorem reflected_contributes_iff_internal
    (x : PhiInt) (c : SectorCert x) :
    Contributes (PhiInt.star x) (reflectedSectorCert x c) ↔
      QseriesFormalization.Ch10.Contributes
        (QseriesFormalization.Ch10.PhiInt.star (toInternalPhi x))
        (QseriesFormalization.Ch10.reflectedSectorCert
          (toInternalPhi x) (toInternalSector c)) := by
  rfl

private def toInternalSplit {p : Nat} (sp : SplitPrimeCert p) :
    QseriesFormalization.Ch10.SplitPrimeCert p where
  π := toInternalPhi sp.π
  hp := sp.hp
  hp10 := sp.hp10
  hnorm := by
    simpa [toInternalPhi, PhiInt.norm,
      QseriesFormalization.Ch10.PhiInt.norm] using sp.hnorm
  hmod2 := by
    simpa [toInternalPhi, toF4,
      QseriesFormalization.Ch10.toF4] using sp.hmod2

private def toInternalAtoms {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    QseriesFormalization.Ch10.PrimeAtomCertificate
      (toInternalSplit sp) (toInternalSector c) where
  sign := atoms.sign
  all_A := by
    intro q hq
    have hqPublic : q ∈ AAtoms ((p - 1) / 10) := by
      simpa only [AAtoms_eq_internal] using hq
    simpa only [AAtomWeight_eq_internal] using atoms.all_A q hqPublic
  all_D := by
    intro q hq
    have hqPublic : q ∈ DAtoms ((p - 1) / 10) := by
      simpa only [DAtoms_eq_internal] using hq
    simpa only [DAtomWeight_eq_internal] using atoms.all_D q hqPublic
  one_atom_bound := by
    simpa only [atomCount_eq_internal] using atoms.one_atom_bound
  atom_of_left_contributes := by
    intro h
    have hPublic : Contributes sp.π c :=
      (contributes_iff_internal sp.π c).mpr h
    simpa only [atomCount_eq_internal] using
      atoms.atom_of_left_contributes hPublic
  atom_of_right_contributes := by
    intro h
    have hPublic :
        Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) :=
      (reflected_contributes_iff_internal sp.π c).mpr h
    simpa only [atomCount_eq_internal] using
      atoms.atom_of_right_contributes hPublic

/-! ## Registered theorems -/

/-- A closed nonmultiplicativity witness for the actual coefficient function. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  simpa only [BCoeff_eq_internal] using
    QseriesFormalization.Ch10.BCoeff_not_multiplicative_witness

/--
Conditional four-valued classification from an explicit split-prime,
sector-label, and finite atom certificate.
-/
theorem prime_coeff_classification {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  simpa only [BCoeff_eq_internal] using
    QseriesFormalization.Ch10.prime_coeff_classification
      (toInternalSplit sp) (toInternalSector c) (toInternalAtoms sp c atoms)

end
end PalomarQseriesPrimeCoefficients
