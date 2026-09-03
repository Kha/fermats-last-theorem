import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_place_eq_of_residue_image
    {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)

    (O : ValuationSubring Fbar) (hOtop : O ≠ ⊤) (hOpir : IsPrincipalIdealRing ↥O)
    (hO : ∀ g : Fbar, g ∈ O ↔ ∃ f : ↥S, R.residue ⟨(f : F), hSR f⟩ = g)

    (hloc : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ R.residue ⟨(f : F), hSR f⟩ ∈ O.nonunits)

    (hrat : ∀ f : ↥S, ∃ a : ↥A, f - ⟨algebraMap L F (a : L), hAS a⟩ ∈ maximalIdeal ↥S) :
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.toValuationSubring = O ∧
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ R.integers), f ∈ S ∧ R.residue ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ R.integers),
        IsUnit f ↔ Q.ord (R.residue ⟨(f : F), hR⟩) = 0 ∧ R.residue ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ R.integers), Q.ord (R.residue ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ R.integers, R.residue ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_eq_of_residue_image.solution
