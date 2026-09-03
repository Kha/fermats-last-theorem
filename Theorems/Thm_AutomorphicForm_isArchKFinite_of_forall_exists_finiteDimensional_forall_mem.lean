import Definitions.Def_AutomorphicForm_ArchKFinite
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isArchKFinite_of_forall_exists_finiteDimensional_forall_mem
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => φ (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) :
    IsArchKFinite F φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchKFinite_of_forall_exists_finiteDimensional_forall_mem.solution
