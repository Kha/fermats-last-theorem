import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_EdgeFamily_isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.EdgeFamily.isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    IsReduced (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_EdgeFamily_isReduced_edgeRingCharP_wittVector_quotient_of_isAlgClosed.solution
