import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_dual_of_isUnit_card

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_dual_of_isUnit_card
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] [Fintype Δ] (hΔ : IsUnit ((Fintype.card Δ : k)))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) :
    finrank k ρ.dual.invariants = finrank k ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_dual_of_isUnit_card.solution
