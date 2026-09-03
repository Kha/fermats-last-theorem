import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ))
    (htrans : Transcendental (AlgebraicClosure ℚ) jb) [Fact (jb ≠ 0)]
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)] :
    ∃ (eη : (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C ⟶
        pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη),
      eη ≫ pullback.snd _ _ = (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase ∧
      (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _})
        (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
          AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom β) ≫
            TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) -
            algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (β b) ∈
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace
            x).toValuationSubring.nonunits) ∧
      (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _})
        (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
          AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom β) ≫
            TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) -
            algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (β b) ∈
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace
            x).toValuationSubring.nonunits) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst _ _ →
        (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ •
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat.solution
