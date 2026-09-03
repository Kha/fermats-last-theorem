import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_M4aHerbrand_GenuineBeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_exists_hasConductorExponentAt_localChar_comp_genuineBeta_le

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.RankinSelberg

theorem NumberField.TateGlobal.exists_hasConductorExponentAt_localChar_comp_genuineBeta_le
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : HeightOneSpectrum (𝓞 ℚ)) (M : ℕ)
    (hμ : ∀ w ∈ primeFibre ℚ K p, ∃ aw : ℕ, aw ≤ M ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar μ w) aw) :
    ∃ e : ℕ, e ≤ M ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p
        (NumberField.TateGlobal.localChar (μ.comp (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K).toMonoidHom)) p) e := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_exists_hasConductorExponentAt_localChar_comp_genuineBeta_le.solution
