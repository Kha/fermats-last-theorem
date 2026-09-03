import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsComplex)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) :
    ∃ β βb : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      IsFactorizableTestFn K βb ∧ IsBiInvariantUnder K U βb ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x →
        IsArchSmoothAtComplex hw (convOp K f x) ∧
        archCasimirAtComplex hw (convOp K f x) = convOp K β x ∧
        archCasimirBarAtComplex hw (convOp K f x) = convOp K βb x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex.solution
