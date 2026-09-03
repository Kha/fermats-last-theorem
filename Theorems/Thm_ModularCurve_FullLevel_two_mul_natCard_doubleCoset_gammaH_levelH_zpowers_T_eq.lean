import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
attribute [-instance] ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

p2m_open "ModularCurve~natCard_orbitRelQuotient_zpowers_T_gamma0_eq_cuspCount ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

theorem ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    2 * Nat.card (DoubleCoset.Quotient (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Set SL(2, ℤ))
          ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      (q ^ 2 - 1) * cuspCount M' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq.solution
