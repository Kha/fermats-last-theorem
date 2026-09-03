import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index

open scoped MatrixGroups in

theorem CohCarrier.index_gammaH_eq_index_gamma0_mul_index (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).index = (CongruenceSubgroup.Gamma0 M).index * H.index := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.solution
