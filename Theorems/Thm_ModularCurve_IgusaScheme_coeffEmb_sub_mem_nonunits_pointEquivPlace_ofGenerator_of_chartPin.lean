import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p))
    [hne : Fact (ModularCurve.CharPModel.jBar p ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))))
    (hFin : ∀ b : chartAlgFin p ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p))))
    (hInf : ∀ b : chartAlgInf p ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo p ℓ) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ)
      (hchartInf : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ),
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgFin p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
        ∀ b : ↥(chartAlgFin p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) ∧
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgInf p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
        ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin.solution
