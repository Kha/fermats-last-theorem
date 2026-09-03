import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_isCoboundary2_of_addEquiv_pi

set_option autoImplicit false
open groupCohomology
theorem groupCohomology.isCoboundary2_of_addEquiv_pi
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G × G → P) (hf : IsCocycle₂ f) : IsCoboundary₂ f := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isCoboundary2_of_addEquiv_pi.solution
