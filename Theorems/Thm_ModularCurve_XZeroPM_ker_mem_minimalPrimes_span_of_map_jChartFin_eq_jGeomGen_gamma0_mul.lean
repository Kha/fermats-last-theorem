import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import P2M.Util
import P2M.Sol.S_ModularCurve_XZeroPM_ker_mem_minimalPrimes_span_of_map_jChartFin_eq_jGeomGen_gamma0_mul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XZeroPM.ker_mem_minimalPrimes_span_of_map_jChartFin_eq_jGeomGen_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hρϖ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0)
    (hρj : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen k M)
    (hρbir : ∀ f : ↥(ModularCurve.modularFunctionFieldC k M), ∃ a b : ↥(Algebra.adjoin k (Set.range ρ)),
        (b : ↥(ModularCurve.modularFunctionFieldC k M)) ≠ 0 ∧ f * b = a) :
    RingHom.ker ρ ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ}).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XZeroPM_ker_mem_minimalPrimes_span_of_map_jChartFin_eq_jGeomGen_gamma0_mul.solution
