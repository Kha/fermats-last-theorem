import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CohCarrier_transfer_transitive

set_option autoImplicit false

theorem CohCarrier.transfer_transitive {G : Type*} [Group G] {C : Type*} [CommGroup C] (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (ψ : K →* C) :
    MonoidHom.transfer ψ
      = MonoidHom.transfer
          (MonoidHom.transfer (ψ.comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_transfer_transitive.solution
