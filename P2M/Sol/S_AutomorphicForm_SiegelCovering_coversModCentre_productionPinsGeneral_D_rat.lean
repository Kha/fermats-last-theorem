import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
import P2M.Util
namespace P2MW.S_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel

private theorem hc : (1/2 : ℝ) ≤ Real.sqrt 3 / 2 := by
  rw [div_le_div_iff_of_pos_right two_pos]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

private theorem hu : (1/2 : ℝ) ≤ 1 := by norm_num
private theorem hd₂ : (0 : ℝ) < 2 := by norm_num
private theorem hd : (1/2 : ℝ) ≤ 2 := by norm_num

theorem solution :
    CoversModCentre ℚ (productionPinsGeneral ℚ).D := by
  rw [productionPinsGeneral_D]
  exact CoversModCentre.mono (centreCutSiegelSet_subset_classRepSiegelSet ℚ (1/2) 1 (1/2) 2)
    (centreCutSiegelSet_coversModCentre_rat hc hu hd₂ hd)
