import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχ : HasConductorExponentAt ℚ v χ a)
    (c : (v.adicCompletion ℚ)ˣ)
    (hc : ∀ u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1),
      (χ u : ℂ) =
        NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1))) :
    ∀ u ∈ higherUnitsAt K w.1 ((a - 1) / 2 + 1),
      ((χ.comp (Units.map (Algebra.norm (v.adicCompletion ℚ)))) u : ℂ) =
        NumberField.StandardAddChar.psiLocal K w.1
          (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) (c : v.adicCompletion ℚ) *
            ((u : w.1.adicCompletion K) - 1)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_comp_norm_apply_eq_psiLocal_algebraMap_mul_sub_one_of_ramificationIdx_eq_one.solution
