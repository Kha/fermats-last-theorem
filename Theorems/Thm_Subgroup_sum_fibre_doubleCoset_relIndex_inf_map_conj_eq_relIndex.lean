import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex

set_option autoImplicit false

open MulAction

theorem Subgroup.sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex
    {G : Type*} [Group G] (H K K' : Subgroup G) (hK : K' ≤ K) (x : G) [K'.IsFiniteRelIndex K]
    [Fintype {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x}] :
    ∑ c : {c : DoubleCoset.Quotient (H : Set G) (K' : Set G) // DoubleCoset.mk H K c.out = DoubleCoset.mk H K x},
      (H ⊓ K'.map (MulAut.conj c.1.out).toMonoidHom).relIndex (H ⊓ K.map (MulAut.conj c.1.out).toMonoidHom) =
        K'.relIndex K := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_sum_fibre_doubleCoset_relIndex_inf_map_conj_eq_relIndex.solution
