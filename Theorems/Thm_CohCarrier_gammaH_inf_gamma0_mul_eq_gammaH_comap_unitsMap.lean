import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) =
      CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap.solution
