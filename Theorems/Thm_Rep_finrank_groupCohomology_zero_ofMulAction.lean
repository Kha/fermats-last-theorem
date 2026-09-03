import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finrank_groupCohomology_zero_ofMulAction
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false
theorem Rep.finrank_groupCohomology_zero_ofMulAction {G : Type} [Group G]
    (X : Type) [MulAction G X] [Finite X] :
    Module.finrank ℤ (groupCohomology (Rep.ofMulActionFinsupp ℤ G X) 0) = Nat.card (MulAction.orbitRel.Quotient G X) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_groupCohomology_zero_ofMulAction.solution
