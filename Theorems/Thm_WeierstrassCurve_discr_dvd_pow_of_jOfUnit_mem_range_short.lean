import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short

set_option autoImplicit false

universe u

theorem WeierstrassCurve.discr_dvd_pow_of_jOfUnit_mem_range_short
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (a b : R₀)
    (hΔ : IsUnit ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).Δ)
    (hj : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).jOfUnit hΔ ∈ Set.range (algebraMap R₀ K)) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ a ^ 3 ∧ (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ b ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short.solution
