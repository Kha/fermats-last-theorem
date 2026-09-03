import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf
attribute [-instance] GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (p : ℕ) [Fact p.Prime]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra (R p) κ]
    (red : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ)
    (hred : ∀ (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) →
        red b = coeffMap (algebraMap (R p) κ) y)
    (ev : κ ⊗[R p] ↥(chartAlgInf p Γ hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p Γ hj), ev (1 ⊗ₜ b) = (red b).coeff 0) :
    Ideal.map (Algebra.TensorProduct.includeRight :
        ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj)) (RingHom.ker red) ∈
      minimalPrimes (κ ⊗[R p] ↥(chartAlgInf p Γ hj)) ∧
    Ideal.map (Algebra.TensorProduct.includeRight :
        ↥(chartAlgInf p Γ hj) →ₐ[R p] κ ⊗[R p] ↥(chartAlgInf p Γ hj)) (RingHom.ker red) ≤ RingHom.ker ev := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf.solution
