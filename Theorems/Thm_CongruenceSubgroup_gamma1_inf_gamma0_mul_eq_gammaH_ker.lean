import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_gamma1_inf_gamma0_mul_eq_gammaH_ker

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.gamma1_inf_gamma0_mul_eq_gammaH_ker (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) =
      CohCarrier.GammaH (N * ℓ) (ZMod.unitsMap (dvd_mul_right N ℓ)).ker := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_gamma1_inf_gamma0_mul_eq_gammaH_ker.solution
