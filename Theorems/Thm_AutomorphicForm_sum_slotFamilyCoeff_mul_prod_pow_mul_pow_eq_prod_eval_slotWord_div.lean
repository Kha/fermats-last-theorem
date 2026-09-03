import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_pow_mul_pow_eq_prod_eval_slotWord_div

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_prod_pow_mul_pow_eq_prod_eval_slotWord_div
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : HeightOneSpectrum (𝓞 K) → ℂ) :
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          ∏ v ∈ T.attach, a v.1 ^ ((m v.1 v.2) 0) *
            ((HeckeEigensystem.cNorm v.1)⁻¹ * b v.1) ^ ((m v.1 v.2) 1) =
      ∏ v ∈ T, MvPolynomial.eval ![a v, b v] (SatakeCombination.slotWord K L ws v (ks v) (js v)) /
          HeckeEigensystem.cNorm (ws v).1 ^ js v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_prod_pow_mul_pow_eq_prod_eval_slotWord_div.solution
