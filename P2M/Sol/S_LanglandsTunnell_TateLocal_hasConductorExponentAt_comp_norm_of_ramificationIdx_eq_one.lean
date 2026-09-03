import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Theorems.Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
import P2M.Util
namespace P2MW.S_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_of_ramificationIdx_eq_one
set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open LanglandsTunnell.TateLocal in

theorem solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : LanglandsTunnell.TateLocal.HasConductorExponentAt E v μ a) :
    LanglandsTunnell.TateLocal.HasConductorExponentAt M w.1
      (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a := by
  have himg := LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one E M v w he
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  ·
    have hmem : Units.map (Algebra.norm (v.adicCompletion E)) u ∈ higherUnitsAt E v a := by
      rw [← himg a]
      exact ⟨u, hu, rfl⟩
    exact ha.1 _ hmem
  ·
    obtain ⟨u, hu, hne⟩ := ha.2 m hm
    have hu' : u ∈ (Units.map (Algebra.norm (v.adicCompletion E))) '' higherUnitsAt M w.1 m := by
      rw [himg m]; exact hu
    obtain ⟨u', hu'mem, rfl⟩ := hu'
    exact ⟨u', hu'mem, hne⟩
