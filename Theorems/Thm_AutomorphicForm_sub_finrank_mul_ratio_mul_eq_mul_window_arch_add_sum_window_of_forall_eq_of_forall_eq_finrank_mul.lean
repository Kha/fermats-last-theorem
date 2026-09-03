import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hST : SK ⊆ T)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')

    (Ia' Ja' Ia Ja : ℂ) (Iv' Jv' Iv Jv : HeightOneSpectrum (𝓞 K) → ℂ)

    (J' J : ℂ)
    (hJ' : J' = cG' * cT'⁻¹ * (Ja' * ∏ v ∈ T, Iv' v + Ia' * ∑ v ∈ T, Jv' v * ∏ u ∈ T.erase v, Iv' u))
    (hJ : J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u))

    (hIa : Ia' = Ia) (hIv : ∀ v ∈ T, Iv' v = Iv v)
    (hJv : ∀ v ∈ T, v ∉ SK → Jv' v = (Module.finrank K L : ℂ) * Jv v) :
    J' - (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * J =
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ((Ja' - (Module.finrank K L : ℂ) * Ja) * ∏ v ∈ T, Iv v +
          Ia * ∑ v ∈ SK, (Jv' v - (Module.finrank K L : ℂ) * Jv v) * ∏ u ∈ T.erase v, Iv u) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sub_finrank_mul_ratio_mul_eq_mul_window_arch_add_sum_window_of_forall_eq_of_forall_eq_finrank_mul.solution
