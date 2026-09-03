import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth
    (p : ℕ) [Fact p.Prime]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : ↥F₀)
    (hsm : Algebra.Smooth ↥(GaloisRep.ratLocalizedAt p)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)))
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (K' : IntermediateField L (LaurentSeries L)) (hK' : K' = ModularCurve.laurentBaseChange L F₀)
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hA : ∀ y : L, IsIntegral ↥(GaloisRep.ratLocalizedAt p) y ↔ ∃ a : A, algebraMap A L a = y)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (x' : ↥K') (hx' : ((x' : LaurentSeries L)) = ModularCurve.coeffEmb L ((x : ↥F₀) : LaurentSeries ℚ)) :
    ∃ e : A ⊗[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)) ≃ₐ[A]
        ↥(TwoChartIntegralModel.chartAlg A ↥K' ({x'} : Set ↥K')),
      ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)),
        (((e (1 ⊗ₜ b) : ↥K') : LaurentSeries L)) =
          ModularCurve.coeffEmb L (((b : ↥F₀) : LaurentSeries ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth.solution
