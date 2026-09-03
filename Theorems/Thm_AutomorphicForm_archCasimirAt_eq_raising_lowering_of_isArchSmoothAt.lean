import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw φ =
      -(1 / 4 : ℂ) • (archDerivAt hw .H (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
          + Complex.I • (archDerivAt hw .E (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
            + archDerivAt hw .Fm (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))))
      - (Complex.I / 2) • (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
      + (1 / 4 : ℂ) • (archDerivAt hw .E (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
          - archDerivAt hw .Fm (archDerivAt hw .E φ - archDerivAt hw .Fm φ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt.solution
