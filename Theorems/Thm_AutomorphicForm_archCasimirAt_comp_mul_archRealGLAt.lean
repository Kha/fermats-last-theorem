import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.archCasimirAt_comp_mul_archRealGLAt
    {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsArchSmoothAt hw φ) (k : GL (Fin 2) ℝ) :
    archCasimirAt hw (fun x => φ (x * archRealGLAt hw k)) = fun x => archCasimirAt hw φ (x * archRealGLAt hw k) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archCasimirAt_comp_mul_archRealGLAt.solution
