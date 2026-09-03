import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ archCutSubmodule F tys)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (hdet : ∀ w : InfinitePlace F,
      ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    (fun x => f (x * k)) ∈ archCutSubmodule F tys := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_comp_mul_mem_archCutSubmodule_of_mem_adelicMaximalCompact_of_det_archComponent_eq_one.solution
