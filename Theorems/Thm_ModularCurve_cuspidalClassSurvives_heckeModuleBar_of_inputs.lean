import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_cuspidalClassSurvives_heckeModuleBar_of_inputs
open ModularCurve AlgebraicCurve
theorem ModularCurve.cuspidalClassSurvives_heckeModuleBar_of_inputs (p : ℕ) [Fact p.Prime]
    (hp : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ))
    (hcomm : HeckeOperatorsCommuteBar p)
    (ha : letI := heckeModuleBar p; ∀ t ∈ eisensteinIdeal p, t • cuspidalClass p = 0)
    (hb : letI := heckeModuleBar p; ∀ x : JZero p, (∀ t ∈ eisensteinIdeal p, t • x = 0) →
      x ∈ eisensteinKernelSubmodule p (heckeModuleBar p) → x = 0)
    (hc : cuspidalClass p ≠ 0) :
    CuspidalClassSurvives p (heckeModuleBar p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspidalClassSurvives_heckeModuleBar_of_inputs.solution
