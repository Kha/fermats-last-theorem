import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
import P2M.Util
namespace P2MW.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

set_option autoImplicit false

namespace M4aP1R

namespace SiegelCovering

theorem centreCutSiegelSet_coversModCentre_rat_impl {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) :=
  AutomorphicForm.SiegelCovering.coversModCentre_centreCutSiegelSet_rat
    (fun g => NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat g) hc hu hd₂ hd

end SiegelCovering

end M4aP1R


theorem solution {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) := by
  exact M4aP1R.SiegelCovering.centreCutSiegelSet_coversModCentre_rat_impl hc hu hd₂ hd
