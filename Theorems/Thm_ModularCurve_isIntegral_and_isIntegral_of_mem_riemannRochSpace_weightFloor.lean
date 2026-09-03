import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

theorem ModularCurve.isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (y : ↥F) (hy : (y : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({y} : Set ↥F)) ↥F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin K ({y} : Set ↥F)) ↥F]
    (m : ℕ) (D : AlgebraicCurve.Divisor K ↥F)
    (hD : ∀ w : AlgebraicCurve.Place K ↥F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0))
    (G : ↥F) (hG : G ∈ AlgebraicCurve.riemannRochSpace D) :
    IsIntegral ↥(Algebra.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K)))
        ((G : LaurentSeries K) ^ 6 * ModularCurve.jqModC K ^ (4 * m) *
          (ModularCurve.jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m)) ∧
      IsIntegral ↥(Algebra.adjoin K ({(ModularCurve.jqModC K)⁻¹} : Set (LaurentSeries K)))
        ((G : LaurentSeries K) ^ 2 * ModularCurve.jqModC K ^ m *
          (ModularCurve.jqModC K - algebraMap K (LaurentSeries K) 1728) ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor.solution
