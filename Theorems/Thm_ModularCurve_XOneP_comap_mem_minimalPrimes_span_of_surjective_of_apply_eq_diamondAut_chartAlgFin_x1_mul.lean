import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneP.comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (ρ : ↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j))
    (hρ : ∀ x, ((ρ x : ↥(chartAlgFin A (↥K) j)) : ↥K) = θ x) (hsurj : Function.Surjective ρ) :
    ∀ 𝔓 ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes, 𝔓.comap ρ ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul.solution
