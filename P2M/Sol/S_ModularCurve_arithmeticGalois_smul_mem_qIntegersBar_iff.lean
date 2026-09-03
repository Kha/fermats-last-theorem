import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_order_coeffMap
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : modularFunctionFieldBar N) :
    arithmeticGalois (modularFunctionFieldFull N) τ • x ∈ qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ↔ x ∈ qIntegersBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  rw [mem_qIntegersBar_iff, mem_qIntegersBar_iff]
  change 0 ≤ ((arithmeticGalois (modularFunctionFieldFull N) τ • x : modularFunctionFieldBar N) :
    LaurentSeries (AlgebraicClosure ℚ)).order ↔ 0 ≤ (x : LaurentSeries (AlgebraicClosure ℚ)).order
  rw [coe_arithmeticGalois_smul, ModularCurve.order_coeffMap (RingHom.injective _)]
