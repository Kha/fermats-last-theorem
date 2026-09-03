import Mathlib.RepresentationTheory.Basic
import P2M.Util
import P2M.Sol.S_Representation_existsUnique_mem_centralizer_apply_eq_of_forall_commute

theorem Representation.existsUnique_mem_centralizer_apply_eq_of_forall_commute
    {k : Type*} [Field k] {Δ : Type*} [Group Δ] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k Δ V)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcomm : ∀ a b : Δ, ρ a * ρ b = ρ b * ρ a)
    (v : V) (hv : v ≠ 0) (w : V) :
    ∃! φ : Module.End k V, (∀ d : Δ, φ * ρ d = ρ d * φ) ∧ φ v = w := by p2m_exact_reverting @_root_.P2MW.S_Representation_existsUnique_mem_centralizer_apply_eq_of_forall_commute.solution
