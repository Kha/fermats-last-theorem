import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_residue_eq_of_integers_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_algEquiv_residue_eq_of_integers_eq
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hint : ∀ f : F, f ∈ R₁.integers ↔ f ∈ R₂.integers) :
    ∃ ι : Fbar₁ ≃ₐ[ResidueField ↥A] Fbar₂,
      ∀ (f : F) (h₁ : f ∈ R₁.integers), ι (R₁.residue ⟨f, h₁⟩) = R₂.residue ⟨f, (hint f).mp h₁⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_residue_eq_of_integers_eq.solution
