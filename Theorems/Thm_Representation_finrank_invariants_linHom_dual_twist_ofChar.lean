import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_Representation_finrank_invariants_linHom_dual_twist_ofChar

set_option autoImplicit false
universe u
open Module
theorem Representation.finrank_invariants_linHom_dual_twist_ofChar
    {k : Type*} [Field k] {Δ : Type*} [Group Δ]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Δ V) (χ : Δ →* kˣ) :
    finrank k ((ρ.dual.twist χ).linHom ((Representation.trivial k Δ k).twist χ)).invariants = finrank k ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_invariants_linHom_dual_twist_ofChar.solution
