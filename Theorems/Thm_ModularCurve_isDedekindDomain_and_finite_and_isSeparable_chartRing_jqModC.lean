import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_JacJ1_ChartAlgebra
import P2M.Util
import P2M.Sol.S_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open Polynomial AlgebraicCurve open ModularCurve hiding finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC
    (p ℓ : ℕ) [Fact p.Prime] [NeZero p] [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (K : Type) [Field K] [CharP K ℓ] [IsAlgClosed K] :
    letI : Algebra K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) :=
      (Polynomial.aeval (R := K)
        (⟨⟨jqModC K, jqModC_mem_full K p⟩,
          CurveModel.adjoin_le_chartRing K _ (Algebra.self_mem_adjoin_singleton K _)⟩ : ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))))).toRingHom.toAlgebra
    IsDedekindDomain ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    Module.Finite K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    NoZeroSMulDivisors K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))) ∧
    (∀ [FaithfulSMul K[X] ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p)))],
      Algebra.IsSeparable (FractionRing K[X]) (FractionRing ↥(CurveModel.chartRing K ({⟨jqModC K, jqModC_mem_full K p⟩} : Set ↥(modularFunctionFieldFullC K p))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isDedekindDomain_and_finite_and_isSeparable_chartRing_jqModC.solution
