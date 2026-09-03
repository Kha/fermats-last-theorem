import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
attribute [-simp] NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.Converse.chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hev : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : ∀ v, v ∉ T → IsUnramifiedCharAt χ v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    chiDetGL 3 (𝓞 ℚ) ℚ χ g =
      ∏ v ∈ T, ((localChar χ v (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ v g)) : ℂˣ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_chiDetGL_eq_prod_localChar_det_componentAt3_of_isArchCompAt_zero_zero.solution
