import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal M4aHerbrand.GenuineDescent LanglandsTunnell.RankinSelberg

theorem NumberField.TateGlobal.finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) :
    ∏ᶠ w ∈ primeFibre E K v, localChar (χ.comp (genuineBaseChange E K).idelicNorm) w (-1) =
      localChar χ v ((-1) ^ Module.finrank E K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one.solution
