import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem ModularCurve.XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hβdef : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hdeg : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L (M * p) p) = p)
    (g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ E : Polynomial ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      E.Monic ∧ E.natDegree = p ∧
      E.map ((ModularCurve.qExpand L p).comp
          ((algebraMap ↥K (LaurentSeries L)).comp
            (algebraMap ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ↥K))) =
        ∏ i : Fin p, (Polynomial.X - Polynomial.C
          (ModularCurve.qTwist (ζ ^ (i : ℕ)) (((g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul.solution
