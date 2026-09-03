import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_linearEquiv_of_finrank_invariants_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
theorem Representation.exists_linearEquiv_of_finrank_invariants_eq {G V W : Type*} [Group G] [Fintype G] [IsCyclic G]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (h : ∀ H : Subgroup G, Module.finrank ℚ (Representation.invariants (ρ.comp H.subtype)) =
      Module.finrank ℚ (Representation.invariants (τ.comp H.subtype))) :
    ∃ e : V ≃ₗ[ℚ] W, ∀ (g : G) (v : V), e (ρ g v) = τ g (e v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_linearEquiv_of_finrank_invariants_eq.solution
