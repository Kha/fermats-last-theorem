import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_coresAdd_comp_inclusion

set_option autoImplicit false

theorem CohCarrier.coresAdd_comp_inclusion {G : Type*} [Group G] {B : Type*} [AddCommGroup B] (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] [(K.subgroupOf L).FiniteIndex] (χ : Additive ↥L →+ B) :
    coresAdd K (χ.comp (Subgroup.inclusion hKL).toAdditive)
      = (K.subgroupOf L).index • coresAdd L χ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_coresAdd_comp_inclusion.solution
