import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, Module.Finite ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) :
    ∃ (n : ℕ) (ρc : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type*) [Group G] (ι : K →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : K) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι (ρ i)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι (ρ i), (∀ y : G, Continuous fun k : K => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.solution
