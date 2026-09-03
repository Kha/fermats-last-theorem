import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped ComplexConjugate

theorem AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) :
    (f ∈ archDualCutSubmodule F tys → (fun x => conj (f x)) ∈ archCutSubmodule F tys) ∧
    (f ∈ archCutSubmodule F tys → (fun x => conj (f x)) ∈ archDualCutSubmodule F tys) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous.solution
