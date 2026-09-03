import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_componentChart_of_discFamily

set_option autoImplicit false

theorem AlgebraicCurve.RegularProlongation.exists_componentChart_of_discFamily
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (N : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar))
    (hne : Nonempty (AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar))
    (disc : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar → Set (AlgebraicCurve.Place L F))
    (coord : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fbar → F)
    (hfam : R.DiscFamily N disc coord) :
    ∃ C : AlgebraicCurve.ComponentChart A F Fbar,
      C.integers = R.integers ∧
      (∀ (f : F) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩) ∧
      C.nodes = N ∧
      (∀ P, P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q) ∧
      (∀ P Q, Q ∉ N → P ∈ disc Q → C.placeMap P = Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_componentChart_of_discFamily.solution
