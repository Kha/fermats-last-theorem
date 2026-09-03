import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_IntegralClosure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (χ : (v.adicCompletion E)ˣ →* ℂˣ) (hχ : HasConductorExponentAt E v χ 0) :
    HasConductorExponentAt M w.1 (χ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero.solution
