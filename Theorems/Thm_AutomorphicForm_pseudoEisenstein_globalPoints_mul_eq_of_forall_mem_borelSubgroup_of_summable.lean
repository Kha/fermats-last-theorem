import Definitions.Def_AutomorphicForm_SlabProfile
import P2M.Util
import P2M.Sol.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
    (F : Type) [Field F] [NumberField F]
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F b * y) = f y)
    (x : AdelicGL2 (𝓞 F) F)
    (hs : Summable fun ξ : F =>
      f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
    (γ : GL (Fin 2) F) :
    Summable (fun ξ : F =>
        f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)
          * (globalPoints (𝓞 F) F γ * x))) ∧
      pseudoEisenstein F f (globalPoints (𝓞 F) F γ * x) = pseudoEisenstein F f x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable.solution
