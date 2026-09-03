import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

theorem NumberField.TateGlobal.localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsIdeleClassChar (𝓞 ℚ) ℚ σ) (hσc : Continuous σ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → IsUnramifiedCharAt σ w)
    (harch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w 0 0) :
    localChar σ v (-1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_localChar_apply_neg_one_eq_one_of_isIdeleClassChar_of_isArchCompAt_zero_zero.solution
