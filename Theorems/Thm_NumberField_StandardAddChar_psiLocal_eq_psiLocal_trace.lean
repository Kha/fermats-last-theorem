import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_eq_psiLocal_trace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.solution
