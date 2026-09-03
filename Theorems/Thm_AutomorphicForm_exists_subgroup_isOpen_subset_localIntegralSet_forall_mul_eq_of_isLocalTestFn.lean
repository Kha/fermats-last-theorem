import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion K)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      (U : Set (GL (Fin 2) (v.adicCompletion K))) ⊆ AutomorphicForm.localIntegralSet K v ∧
      ∀ g : GL (Fin 2) (v.adicCompletion K), ∀ u₁ ∈ U, ∀ u₂ ∈ U, fv (u₁ * g * u₂) = fv g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn.solution
