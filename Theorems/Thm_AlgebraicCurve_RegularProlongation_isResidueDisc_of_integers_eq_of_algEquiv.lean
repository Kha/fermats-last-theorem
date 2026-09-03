import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_isResidueDisc_of_integers_eq_of_algEquiv

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.isResidueDisc_of_integers_eq_of_algEquiv
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hint : ∀ f : F, f ∈ R₁.integers ↔ f ∈ R₂.integers)
    (ι : Fbar₁ ≃ₐ[ResidueField ↥A] Fbar₂)
    (hι : ∀ (f : F) (h₁ : f ∈ R₁.integers), ι (R₁.residue ⟨f, h₁⟩) = R₂.residue ⟨f, (hint f).mp h₁⟩)
    {Q₁ : Place (ResidueField ↥A) Fbar₁} {Q₂ : Place (ResidueField ↥A) Fbar₂}
    (hQ : ∀ x : Fbar₁, x ∈ Q₁.toValuationSubring ↔ ι x ∈ Q₂.toValuationSubring)
    {D : Set (Place L F)} {z : F}
    (h : R₁.IsResidueDisc Q₁ D z) :
    R₂.IsResidueDisc Q₂ D z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_isResidueDisc_of_integers_eq_of_algEquiv.solution
