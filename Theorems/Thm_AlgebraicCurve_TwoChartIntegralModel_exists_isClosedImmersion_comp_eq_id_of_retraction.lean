import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk AlgebraicCurve~isClosed_singleton_of_ne_genericPoint AlgebraicCurve.TwoChartIntegralModel"
open scoped TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem AlgebraicCurve.TwoChartIntegralModel.exists_isClosedImmersion_comp_eq_id_of_retraction
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₀ : Type u) [Field F₀] [Algebra R F₀] (j₀ : F₀) [Fact (j₀ ≠ 0)]
    [IsProper (toBase R F j)] [IsProper (toBase R F₀ j₀)]

    (π : TwoChartIntegralModel R F j ⟶ TwoChartIntegralModel R F₀ j₀) (hπ : π ≫ toBase R F₀ j₀ = toBase R F j)
    (ι : ↥(chartAlgFin R F₀ j₀) →ₐ[R] ↥(chartAlgFin R F j))
    (hπchart : ιFin R F j ≫ π = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ιFin R F₀ j₀)

    (κ : Type u) [Field κ] [Algebra R κ]
    [IsIntegral (pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [SmoothOfRelativeDimension 1
      (pullback.snd (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))]
    [Nontrivial (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))]

    (πκ : pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hπκfst : πκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π)
    (hπκsnd : πκ ≫ pullback.snd _ _ = pullback.snd _ _)

    (c₀ : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F₀ j₀))) ⟶
      pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀))).toRingHom) ≫ ιFin R F₀ j₀)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F₀ j₀)))))
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (σ₀ : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] κ ⊗[R] ↥(chartAlgFin R F₀ j₀))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) ι z) = z) :
    ∃ comp₀ : pullback (toBase R F₀ j₀) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      comp₀ ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion comp₀ ∧
      comp₀ ≫ πκ = 𝟙 _ ∧
      c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧

      (∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isClosedImmersion_comp_eq_id_of_retraction.solution
