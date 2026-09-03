import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    arithmeticGalois (modularFunctionFieldFull N) τ • cuspInftyBar N = cuspInftyBar N := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring, cuspInftyBar_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  exact ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff N τ⁻¹ x
