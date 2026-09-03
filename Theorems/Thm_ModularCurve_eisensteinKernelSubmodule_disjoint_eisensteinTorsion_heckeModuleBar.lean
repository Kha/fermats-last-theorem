import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinKernelSubmodule_disjoint_eisensteinTorsion_heckeModuleBar
open ModularCurve AlgebraicCurve
theorem ModularCurve.eisensteinKernelSubmodule_disjoint_eisensteinTorsion_heckeModuleBar (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ x : JZero p, (∀ t ∈ eisensteinIdeal p, t • x = 0) →
      x ∈ eisensteinKernelSubmodule p (heckeModuleBar p) → x = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinKernelSubmodule_disjoint_eisensteinTorsion_heckeModuleBar.solution
