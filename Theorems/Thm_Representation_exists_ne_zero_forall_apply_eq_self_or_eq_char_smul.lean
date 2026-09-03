import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul

theorem Representation.exists_ne_zero_forall_apply_eq_self_or_eq_char_smul
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V]
    (ρ : Representation k G V) (χ : G →* kˣ)
    (h : ∀ (g : G) (v : V), ρ g (ρ g v - (χ g : k) • v) = ρ g v - (χ g : k) • v) :
    ∃ v : V, v ≠ 0 ∧ ((∀ g : G, ρ g v = v) ∨ (∀ g : G, ρ g v = (χ g : k) • v)) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_ne_zero_forall_apply_eq_self_or_eq_char_smul.solution
