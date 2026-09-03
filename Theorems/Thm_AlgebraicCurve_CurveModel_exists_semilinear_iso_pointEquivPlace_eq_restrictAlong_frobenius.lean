import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius
    (k : Type*) (K : Type u) (F₀ : Type*) (F : Type v) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (M : CurveModel K F) :
    ∃ σ : K →+* K, (∀ c : K, σ c = c ^ Nat.card k) ∧
      ∃ B : M.C ≅ M.C, B.hom ≫ M.toBase ≫ Spec.map (CommRingCat.ofHom σ) = M.toBase ∧
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
          ∃ hy : (Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom) ≫ M.toBase = 𝟙 _,
            M.pointEquivPlace ⟨Spec.map (CommRingCat.ofHom σ) ≫ y.1 ≫ B.hom, hy⟩ =
              AlgebraicCurve.Place.restrictAlong φ hφi (M.pointEquivPlace y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_semilinear_iso_pointEquivPlace_eq_restrictAlong_frobenius.solution
