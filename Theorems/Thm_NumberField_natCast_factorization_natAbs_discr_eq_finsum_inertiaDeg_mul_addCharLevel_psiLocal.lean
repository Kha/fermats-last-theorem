import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal~addCharLevel_psiLocal_eq_count_differentIdeal"

theorem NumberField.natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) :
    (((discr K).natAbs.factorization (Ideal.absNorm v.asIdeal) : ℕ) : ℤ) =
      ∑ᶠ w ∈ primeFibre ℚ K v,
        (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * addCharLevel (psiLocal K w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_natCast_factorization_natAbs_discr_eq_finsum_inertiaDeg_mul_addCharLevel_psiLocal.solution
