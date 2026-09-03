import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt
    (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) :
    psiLocal ℚ p x = psiQ (adeleSingleAt ℚ p x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt.solution
