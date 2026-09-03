import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) :
    archDerivAtComplex hw .H (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .H φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .H φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .E φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iE φ) =
      (1 : ℂ) • archDerivAtComplex hw .iH φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .E φ) - archDerivAtComplex hw .E (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .iE φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .Fm φ) - archDerivAtComplex hw .Fm (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .iFm φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .iH φ) =
      (-2 : ℂ) • archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iH (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iH φ) =
      (2 : ℂ) • archDerivAtComplex hw .Fm φ ∧
    archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) =
      (-1 : ℂ) • archDerivAtComplex hw .H φ ∧
    archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ) - archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ) =
      0 ∧
    archDerivAtComplex hw .E (archDerivAtComplex hw .iE φ) - archDerivAtComplex hw .iE (archDerivAtComplex hw .E φ) =
      0 ∧
    archDerivAtComplex hw .Fm (archDerivAtComplex hw .iFm φ) - archDerivAtComplex hw .iFm (archDerivAtComplex hw .Fm φ) =
      0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex.solution
