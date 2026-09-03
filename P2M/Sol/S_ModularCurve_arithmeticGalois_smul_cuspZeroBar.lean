import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_cuspZeroBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    arithmeticGalois (modularFunctionFieldFull N) τ • cuspZeroBar N = cuspZeroBar N := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring, cuspZeroBar_def, Place.smul_toValuationSubring,
    cuspInftyBar_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, frickeInvolutionBar_def, ← map_inv]
  change geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)⁻¹
      (arithmeticGalois (modularFunctionFieldFull N) τ⁻¹ • x) ∈ _ ↔
    geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)⁻¹ x ∈ _
  rw [← ModularCurve.arithmeticGalois_smul_geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ⁻¹ (frickeInvolutionFull N)⁻¹ x]
  exact ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff N τ⁻¹ _
