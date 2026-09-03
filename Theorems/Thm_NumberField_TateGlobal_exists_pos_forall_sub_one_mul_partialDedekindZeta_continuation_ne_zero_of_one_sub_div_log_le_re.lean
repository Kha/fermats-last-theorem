import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im|) ≤ s.re → Z s ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re.solution
