import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
attribute [-simp] ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg

set_option autoImplicit false
theorem ModularCurve.exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ OE : ValuationSubring ↥(IntermediateField.adjoin L ({j} : Set ↥K)),

      IsDiscreteValuationRing ↥OE ∧

      (∀ e : ↥(IntermediateField.adjoin L ({j} : Set ↥K)), e ∈ OE ↔ ((e : ↥K) ∈ W₀)) ∧

      (∀ e : ↥(IntermediateField.adjoin L ({j} : Set ↥K)), e ∈ OE ↔
        ∃ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 ∧
          (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P) ∧

      (∀ (e : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) (P Q : Polynomial A),
        Q.map (IsLocalRing.residue A) ≠ 0 → (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P →
        (e ∈ OE.nonunits ↔ P.map (IsLocalRing.residue A) = 0)) ∧

      (∀ ϖ : A, Irreducible ϖ → ∃ ϖO : ↥OE,
        ((ϖO : ↥(IntermediateField.adjoin L ({j} : Set ↥K))) : ↥K) = algebraMap A ↥K ϖ ∧ Irreducible ϖO) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC.solution
