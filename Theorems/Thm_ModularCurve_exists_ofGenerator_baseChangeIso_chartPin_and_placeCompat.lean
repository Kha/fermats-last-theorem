import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
    (N : ℕ) [NeZero N]

    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]

    (cFin : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))))
    (hcFin : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)),
      ((cFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N)))
    (cInf : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hcInf : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
      ((cInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) := CurveModel.ofGenerator ℚ (jFull N) htrans₀
    ∃ (eη : Mη.C ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (_ : IsIso eη),
      eη ≫ pullback.snd _ _ = Mη.toBase ∧
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y₀ : closedPoints M₀.C),
      (y.1 ≫ eη ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = y₀.1 →
      ((Mη.pointEquivPlace y).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint y₀).toValuationSubring.toSubring)) ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N)) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ιInf ℚ (jFull N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat.solution
