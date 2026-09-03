import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] (hqN : ¬ q ∣ N)
    (k₀ : Subfield k) (v : Place k (modularFunctionFieldC k N))
    (hv : (jGeomGen k N : ↥(modularFunctionFieldC k N)) ∈ v.toValuationSubring)
    (f : ↥(modularFunctionFieldC k N))
    (hf₀ : f ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}))
    (hf : f ∈ v.toValuationSubring) :
    ∃ a s : ↥(modularFunctionFieldC k N),
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) a ∧
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) s ∧
      a ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) ∧
      s ∈ Subfield.closure (Set.range (fun c : ↥k₀ => algebraMap k ↥(modularFunctionFieldC k N) (c : k)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) ∧
      (∀ n : ℤ, ((a : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ∈ k₀) ∧
      (∀ n : ℤ, ((s : ↥(modularFunctionFieldC k N)) : LaurentSeries k).coeff n ∈ k₀) ∧
      s ≠ 0 ∧ s ∈ v.toValuationSubring ∧ s⁻¹ ∈ v.toValuationSubring ∧
      f * s = a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring.solution
