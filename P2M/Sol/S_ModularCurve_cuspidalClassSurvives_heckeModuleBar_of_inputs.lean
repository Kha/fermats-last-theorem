import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
namespace P2MW.S_ModularCurve_cuspidalClassSurvives_heckeModuleBar_of_inputs
open ModularCurve AlgebraicCurve

theorem solution (p : ℕ) [Fact p.Prime]
    (hp : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ))
    (hcomm : HeckeOperatorsCommuteBar p)
    (ha : letI := heckeModuleBar p; ∀ t ∈ eisensteinIdeal p, t • cuspidalClass p = 0)
    (hb : letI := heckeModuleBar p; ∀ x : JZero p, (∀ t ∈ eisensteinIdeal p, t • x = 0) →
      x ∈ eisensteinKernelSubmodule p (heckeModuleBar p) → x = 0)
    (hc : cuspidalClass p ≠ 0) :
    CuspidalClassSurvives p (heckeModuleBar p) := by
  have _ := hp
  have _ := hcomm
  intro hmem
  exact hc (hb (cuspidalClass p) ha hmem)
