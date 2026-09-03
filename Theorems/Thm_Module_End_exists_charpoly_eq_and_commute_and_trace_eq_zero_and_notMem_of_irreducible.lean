import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible

set_option autoImplicit false

open Polynomial

universe u v w

theorem Module.End.exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
    {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2)
    {H : Type w} [Group H] (ρ : H →* Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    (U : AddSubgroup (Module.End k V))
    (hU : ∀ h : H, ∀ m ∈ U, ρ h * m * ρ h⁻¹ ∈ U)
    (hproper : ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m ∉ U) :
    ∃ h : H, ∃ α β : k, α ≠ β ∧ (ρ h).charpoly = (X - C α) * (X - C β) ∧
      ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m * ρ h = ρ h * m ∧ m ∉ U := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.solution
