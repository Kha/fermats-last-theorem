import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
    (hψ0 : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
      algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0)
    (hord : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∀ k : ℤ, k < 0 →
      (((f : ↥K) : LaurentSeries L)).coeff k = 0) :
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀) ∧
    (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ((b : ↥K)) ∈ W₀.nonunits →
      ψ b ∈ IsLocalRing.maximalIdeal A) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_maximalIdeal_apply_of_coe_mem_nonunits_gauss_of_mem_chartAlgInf_laurentBaseChange.solution
