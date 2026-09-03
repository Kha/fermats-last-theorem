import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinQuotientInvariantsFiniteAt_heckeModuleBar_of_fg_of_isTorsion
open ModularCurve AlgebraicCurve
theorem ModularCurve.eisensteinQuotientInvariantsFiniteAt_heckeModuleBar_of_fg_of_isTorsion (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hfg : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (htors : letI := heckeModuleBar p
      ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p), ∃ n : ℕ, 0 < n ∧ n • z = 0) :
    EisensteinQuotientInvariantsFiniteAt p (heckeModuleBar p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinQuotientInvariantsFiniteAt_heckeModuleBar_of_fg_of_isTorsion.solution
