import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff

set_option autoImplicit false

theorem Subgroup.nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff
    {U G : Type*} [CommGroup U] [Group G] [Finite U]
    (Ψ : U →* G) (hΨ : Function.Surjective Ψ)
    (c : U) (hc : Ψ c = 1) (hcard : Nat.card G = (Subgroup.zpowers c).index)
    (H : Subgroup U) (hcH : c ∈ H) (I : Subgroup G) (hI : ∀ u : U, Ψ u ∈ I ↔ u ∈ H) :
    Nonempty (↥H ⧸ Subgroup.zpowers (⟨c, hcH⟩ : ↥H) ≃* ↥I) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_nonempty_quotient_zpowers_mulEquiv_of_forall_apply_mem_iff.solution
