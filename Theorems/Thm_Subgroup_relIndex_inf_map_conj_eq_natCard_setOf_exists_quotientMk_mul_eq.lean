import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq

set_option autoImplicit false

theorem Subgroup.relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq
    {G : Type*} [Group G] (K : Subgroup G) (g : G) :
    (K ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex K =
      Nat.card {c : G ⧸ K // ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq.solution
