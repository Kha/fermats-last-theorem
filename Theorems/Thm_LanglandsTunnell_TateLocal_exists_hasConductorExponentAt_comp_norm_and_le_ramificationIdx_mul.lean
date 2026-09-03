import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : LanglandsTunnell.TateLocal.HasConductorExponentAt E v μ a) :
    ∃ b' : ℕ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt M w.1
        (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) b' ∧
      b' ≤ v.asIdeal.ramificationIdx' w.1.asIdeal * a := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_comp_norm_and_le_ramificationIdx_mul.solution
