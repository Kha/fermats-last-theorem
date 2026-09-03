import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (lam nu : (v.adicCompletion K)ˣ →* ℂˣ) (a b : ℕ)
    (hlam : HasConductorExponentAt K v lam a) (hnu : HasConductorExponentAt K v nu b) (hlt : b < a) :
    HasConductorExponentAt K v (lam * nu) a := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_of_lt.solution
