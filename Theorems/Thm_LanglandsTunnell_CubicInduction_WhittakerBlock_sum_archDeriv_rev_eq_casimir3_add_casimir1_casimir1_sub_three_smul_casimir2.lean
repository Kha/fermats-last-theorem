import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) :
    (fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDeriv i j (archDeriv k i (archDeriv j k F)) g) =
      casimir3 F + casimir1 (casimir1 F) - (3 : ℂ) • casimir2 F := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_sum_archDeriv_rev_eq_casimir3_add_casimir1_casimir1_sub_three_smul_casimir2.solution
