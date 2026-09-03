import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S S' : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ k : K, ∀ s ∈ S', (fun x => s (x * ι k)) ∈ S')
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : K) (s : S),
      (θ ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ : G → ℂ) = fun x => (θ s : G → ℂ) (x * ι k))
    (hSA : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    S' ≤ ⨆ i, typeSubmodule ι (ρ i) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule.solution
