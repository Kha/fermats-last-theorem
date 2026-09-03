import Definitions.Def_LanglandsTunnell_JLData
import Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_nonempty_sOrderReps

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.Converse

private theorem sunitRep_valued_localOf {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (α : Kˣ) :
    Valued.v ((localOf K v α : (v.adicCompletion K)ˣ) : v.adicCompletion K) = v.valuation K (α : K) := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) (v := v) (α : K)

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Nonempty (SOrderReps K S) := by
  refine ⟨⟨fun n => Units.mk0 (Classical.choose (exists_ne_zero_valuation_eq_exp_neg K S n))
    (Classical.choose_spec (exists_ne_zero_valuation_eq_exp_neg K S n)).1, fun n v => ?_⟩⟩
  rw [sunitRep_valued_localOf]
  exact (Classical.choose_spec (exists_ne_zero_valuation_eq_exp_neg K S n)).2 v
