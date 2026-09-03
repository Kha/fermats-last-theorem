import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : LanglandsTunnell.TateLocal.HasConductorExponentAt E v μ a) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt M w.1
      (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one.solution
