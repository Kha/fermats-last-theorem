import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV

set_option autoImplicit false

open IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_rat_eq_psiV
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    psiLocal ℚ v = psiV v := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV.solution
