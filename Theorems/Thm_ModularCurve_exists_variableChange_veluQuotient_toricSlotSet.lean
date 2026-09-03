import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_variableChange_veluQuotient_toricSlotSet
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.exists_variableChange_veluQuotient_toricSlotSet (K : Type*) [Field K]
    [CharZero K] (p : ℕ) [NeZero p] (hp : Odd p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hE : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY) :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (p : LaurentSeries K) ∧
        C.r = HahnSeries.C (((p : K) ^ 2 - 1) / 12) ∧
          C.s = HahnSeries.C (((p : K) - 1) / 2) ∧
            C.t = HahnSeries.C (-(((p : K) ^ 2 - 1) / 24)) ∧
              C • (tateBase K p).veluQuotient (toricSlotSet K p ζ) =
                (tateLaurent K).map (qExpand K (p * p)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricSlotSet.solution
