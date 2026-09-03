import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero.solution
