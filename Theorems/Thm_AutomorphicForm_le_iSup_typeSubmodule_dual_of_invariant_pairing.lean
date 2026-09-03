import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing
    {K : Type*} [Group K] {G : Type*} [Group G]
    (ι : K →* G) (hι : Function.Injective ι) {n : ℕ}
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i))
    (S T : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k : K, ∀ s ∈ S, (fun x => s (x * ι k)) ∈ S) (hT : ∀ k : K, ∀ t ∈ T, (fun x => t (x * ι k)) ∈ T)
    (β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ)
    (hβ : ∀ (k : K) (s : S) (t : T), β ⟨fun x => (s : G → ℂ) (x * ι k), hS k s s.2⟩ ⟨fun x => (t : G → ℂ) (x * ι k), hT k t t.2⟩ = β s t)
    (hnd : ∀ t : T, (∀ s : S, β s t = 0) → t = 0)
    (hSle : S ≤ ⨆ i, typeSubmodule ι (ρ i)) :
    T ≤ ⨆ i, typeSubmodule ι (ρ i).dual := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing.solution
