import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation

set_option autoImplicit false
open groupCohomology
theorem groupCohomology.exists_div_mem_of_isMulCocycle1_of_presentation
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
    (Fn Fn1 : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn1 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation.solution
