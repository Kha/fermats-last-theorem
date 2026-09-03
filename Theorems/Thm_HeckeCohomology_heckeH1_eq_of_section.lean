import Definitions.Def_GroupCohomology_TransferHecke
import P2M.Util
import P2M.Sol.S_HeckeCohomology_heckeH1_eq_of_section

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in
open groupCohomology in

theorem HeckeCohomology.heckeH1_eq_of_section {k Γ : Type} [CommRing k] [Group Γ]
    (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ) [S₂.FiniteIndex]
    (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ)
    (r : Quotient (QuotientGroup.rightRel S₂) → Γ)
    (σ : Quotient (QuotientGroup.rightRel S₂) → Γ → S₂)
    (hσ : ∀ q γ, (σ q γ : Γ) = r q * γ * (r (cls S₂ (r q * γ)))⁻¹)
    (f g : cocycles₁ A)
    (hg : ∀ γ : Γ, g γ = ∑ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (r q)⁻¹ (φ (f (c (σ q γ) : Γ)))) :
    H1π A g = heckeH1 S₁ S₂ c A φ hφ (H1π A f) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_heckeH1_eq_of_section.solution
