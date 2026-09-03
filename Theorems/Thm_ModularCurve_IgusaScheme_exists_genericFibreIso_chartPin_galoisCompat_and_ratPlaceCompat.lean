import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme~exists_genericFibreIso_chartPin_and_galoisCompat AlgebraicCurve"
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    (eFin₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin₀ : ∀ b : chartAlgFin N ℓ,
      ((eFin₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (eInf₀ : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf₀ : ∀ b : chartAlgInf N ℓ,
      ((eInf₀ (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    ∃ (eη : Mη.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (igusaTo N ℓ) _ = Mη.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf N ℓ) ∧
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x) ∧
      let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) :=
        CurveModel.ofGenerator ℚ (jFull N) htrans₀
      ∃ (e₀ : M₀.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) (_ : IsIso e₀),
        e₀ ≫ pullback.snd (igusaTo N ℓ) _ = M₀.toBase ∧
        (AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (eFin₀.toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
            ModularCurve.IgusaScheme.ιFin N ℓ) ∧
        (AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (eInf₀.toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
            ModularCurve.IgusaScheme.ιInf N ℓ) ∧
        ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
          (x₀ : closedPoints M₀.C),
        y ≫ pullback.fst (igusaTo N ℓ) _ = x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
        ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
            ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
              (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
                (B := ↥(modularFunctionFieldFull N))).toRingHom) =
          (M₀.placeOfPoint x₀).toValuationSubring.toSubring) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_galoisCompat_and_ratPlaceCompat.solution
