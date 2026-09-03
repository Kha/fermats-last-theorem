import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.continuous_archFlowAt_and_continuous_archFlowAtComplex
    (K : Type) [Field K] [NumberField K] :
    (∀ (w : InfinitePlace K) (hw : w.IsReal) (d : ArchDir), Continuous fun t : ℝ => archFlowAt hw d t) ∧
    (∀ (w : InfinitePlace K) (hw : w.IsComplex) (d : ArchDirComplex), Continuous fun t : ℝ => archFlowAtComplex hw d t) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex.solution
