import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (x : (v.adicCompletion E)ˣ) :
    x ∈ (Units.map (Algebra.norm (v.adicCompletion E) (S := w.1.adicCompletion M) :
        w.1.adicCompletion M →* v.adicCompletion E)).range ↔
      ∃ k : ℤ, Valued.v (x : v.adicCompletion E) =
        WithZero.exp ((Ideal.inertiaDeg' v.asIdeal w.1.asIdeal : ℤ) * k) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_mem_range_unitsMap_norm_iff_inertiaDeg_dvd_of_ramificationIdx_eq_one.solution
