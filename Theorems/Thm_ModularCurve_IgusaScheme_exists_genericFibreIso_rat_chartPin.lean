import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_genericFibreIso_rat_chartPin
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_genericFibreIso_rat_chartPin
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (htrans : Transcendental ℚ (jFull N))
    [hne : Fact (jFull N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    (eFin : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin : ∀ b : chartAlgFin N ℓ,
      ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (eInf : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf : ∀ b : chartAlgInf N ℓ,
      ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N))) :
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) :=
      CurveModel.ofGenerator ℚ (jFull N) htrans
    ∃ (e₀ : M₀.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) (_ : IsIso e₀),
      e₀ ≫ pullback.snd (igusaTo N ℓ) _ = M₀.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_rat_chartPin.solution
