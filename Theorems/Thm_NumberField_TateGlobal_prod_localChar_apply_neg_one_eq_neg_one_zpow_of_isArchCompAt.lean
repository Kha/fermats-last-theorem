import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse

theorem NumberField.TateGlobal.prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsIdeleClassChar (𝓞 ℚ) ℚ σ) (hσc : Continuous σ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → IsUnramifiedCharAt σ w)
    (t : ℂ) (a : ℤ) (harch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t a) :
    ∏ w ∈ S, ((localChar σ w (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt.solution
