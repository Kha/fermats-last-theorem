import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup

set_option autoImplicit false

universe u
theorem Representation.exists_ne_zero_forall_apply_eq_of_isPGroup
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_ne_zero_forall_apply_eq_of_isPGroup.solution
