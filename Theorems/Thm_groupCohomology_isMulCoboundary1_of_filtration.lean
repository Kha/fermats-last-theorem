import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_isMulCoboundary1_of_filtration

set_option autoImplicit false
open groupCohomology
theorem groupCohomology.isMulCoboundary1_of_filtration
    {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ (n : ℕ) (g : G) (x : M), x ∈ F n → g • x ∈ F n)
    (hcomplete : ∀ s : ℕ → M, (∀ n, s (n + 1) / s n ∈ F n) → ∃ x : M, ∀ n, x / s n ∈ F n)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 1)
    (hgr : ∀ (n : ℕ) (f : G → M), (∀ g, f g ∈ F n) → IsMulCocycle₁ f →
      ∃ a ∈ F n, ∀ g, f g / (g • a / a) ∈ F (n + 1))
    (f : G → M) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isMulCoboundary1_of_filtration.solution
