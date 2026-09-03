import Mathlib
import P2M.Util
import P2M.Sol.S_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj

theorem DoubleCoset.natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj
    {G : Type*} [Group G] {Γ U : Subgroup G} (V : Subgroup G) (hΓU : Γ ≤ U) (β : G) :
    Nat.card {q : DoubleCoset.Quotient (Γ : Set G) (V : Set G) //
        ∃ g : G, DoubleCoset.mk Γ V g = q ∧ DoubleCoset.mk U V g = DoubleCoset.mk U V β}
      = Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf U : Subgroup U) : Set U)
          (((U ⊓ V.map (MulAut.conj β).toMonoidHom).subgroupOf U : Subgroup U) : Set U)) := by p2m_exact_reverting @_root_.P2MW.S_DoubleCoset_natCard_fibre_quotient_eq_natCard_quotient_inf_map_conj.solution
