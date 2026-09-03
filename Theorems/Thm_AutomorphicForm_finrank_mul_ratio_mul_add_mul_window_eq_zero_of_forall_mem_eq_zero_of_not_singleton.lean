import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hST : SK ⊆ T)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')

    (Ia Ja Ja' : ℂ) (Iv Jv Jv' : HeightOneSpectrum (𝓞 K) → ℂ)

    (J : ℂ)
    (hJ : J = cG * cT⁻¹ * (Ja * ∏ v ∈ T, Iv v + Ia * ∑ v ∈ T, Jv v * ∏ u ∈ T.erase v, Iv u))

    (P : Finset (HeightOneSpectrum (𝓞 K))) (hPT : P ⊆ T) (b : Prop)
    (hne : P.Nonempty ∨ b) (hnot1 : ¬ (P.card = 1 ∧ ¬ b))
    (hIv : ∀ v ∈ P, Iv v = 0)
    (hIa : b → Ia = 0) (hJa' : b → Ja' = 0) :
    (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * J +
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ((Ja' - (Module.finrank K L : ℂ) * Ja) * ∏ v ∈ T, Iv v +
          Ia * ∑ v ∈ SK, (Jv' v - (Module.finrank K L : ℂ) * Jv v) * ∏ u ∈ T.erase v, Iv u) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finrank_mul_ratio_mul_add_mul_window_eq_zero_of_forall_mem_eq_zero_of_not_singleton.solution
