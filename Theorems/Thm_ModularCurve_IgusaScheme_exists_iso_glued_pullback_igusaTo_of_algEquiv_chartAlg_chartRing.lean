import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K]
    {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (eFin : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t} : Set L)))
    (eInf : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hjInv : ((eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)) : L) = t⁻¹)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n)) :
    ∃ (es : AlgebraicCurve.CurveModel.glued K t ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) (_ : IsIso es),
      es ≫ pullback.snd (igusaTo N ℓ) _ = AlgebraicCurve.CurveModel.gluedToBase K t ∧
      (AlgebraicCurve.CurveModel.ι₀ K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing.solution
