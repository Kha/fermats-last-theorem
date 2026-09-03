import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
    (q : ℕ) [Fact q.Prime] (ℓg : ℕ) [Fact ℓg.Prime] (hℓg3 : 3 ≤ ℓg)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (hℓgM' : ℓg ∣ M') :
    2 * (CohCarrier.GammaH (q ^ 2 * M')
          (levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * (ℓg - 1) * dedekindPsi M' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq.solution
