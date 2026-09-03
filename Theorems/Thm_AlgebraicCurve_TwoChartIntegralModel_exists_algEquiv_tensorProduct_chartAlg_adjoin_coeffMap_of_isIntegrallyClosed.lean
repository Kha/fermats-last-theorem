import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed
    (R : Type) [CommRing R] [IsDomain R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F₀ : IntermediateField K₀ (LaurentSeries K₀)) [Algebra R ↥F₀] [IsScalarTower R K₀ ↥F₀]
    (x : ↥F₀) [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ ({x} : Set ↥F₀)) ↥F₀]
    [Module.Flat R ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀))]
    (L : Type) [Field L] (i : K₀ →+* L)
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = IntermediateField.adjoin L (⇑(ModularCurve.coeffMap i) '' (F₀ : Set (LaurentSeries K₀))))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra R A] (hRA : ∀ r : R, algebraMap A L (algebraMap R A r) = i (algebraMap R K₀ r))
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (x' : ↥K') (hx' : ((x' : ↥K') : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥F₀) : LaurentSeries K₀))
    [IsDomain (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)))]
    [IsIntegrallyClosed (A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)))] :
    ∃ e : A ⊗[R] ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)) ≃ₐ[A] ↥(chartAlg A ↥K' ({x'} : Set ↥K')),
      ∀ b : ↥(chartAlg R ↥F₀ ({x} : Set ↥F₀)),
        (((e (1 ⊗ₜ[R] b) : ↥K') : LaurentSeries L)) = ModularCurve.coeffMap i ((b : ↥F₀) : LaurentSeries K₀) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensorProduct_chartAlg_adjoin_coeffMap_of_isIntegrallyClosed.solution
