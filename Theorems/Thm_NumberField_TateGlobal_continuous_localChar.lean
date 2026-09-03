import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_continuous_localChar

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.continuous_localChar {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ⇑(localChar χ v) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_continuous_localChar.solution
