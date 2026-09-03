import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top

set_option autoImplicit false

theorem Module.End.rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0)
    (𝒜 : Set (Module.End ℂ V))
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A * B = B * A)
    (hirr : ∀ W : Submodule ℂ V, (∀ A ∈ 𝒜, ∀ x ∈ W, A x ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.rank ℂ V ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_rank_le_one_of_countable_of_commute_of_forall_invariant_eq_bot_or_eq_top.solution
