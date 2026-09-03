import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_coresAdd_comp_subtype

set_option autoImplicit false

theorem CohCarrier.coresAdd_comp_subtype {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive G →+ B) :
    coresAdd K (φ.comp (Subgroup.subtype K).toAdditive) = K.index • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_coresAdd_comp_subtype.solution
