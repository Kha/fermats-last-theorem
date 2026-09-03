import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple

set_option autoImplicit false
universe u
open Module
theorem Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k] [CharP k p]
    {Δ : Type*} [Group Δ] [Finite Δ] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Δ V) (hV : Module.finrank k V ≠ 0)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Δ) [P.Normal] (hP : IsPGroup p P) :
    ∀ x ∈ P, ρ x = 1 := by p2m_exact_reverting @_root_.P2MW.S_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple.solution
