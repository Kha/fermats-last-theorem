import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers

set_option autoImplicit false

theorem LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) (hx : x ∈ v.adicCompletionIntegers K) :
    NumberField.StandardAddChar.psiLocal K v x = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers.solution
