import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_weierstrassP_scale

set_option autoImplicit false

theorem PeriodPair.weierstrassP_scale (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_weierstrassP_scale.solution
