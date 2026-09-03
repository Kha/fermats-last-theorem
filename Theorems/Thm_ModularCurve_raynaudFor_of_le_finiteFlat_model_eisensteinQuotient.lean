import Mathlib
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_raynaudFor_of_le_finiteFlat_model_eisensteinQuotient

open ModularCurve
theorem ModularCurve.raynaudFor_of_le_finiteFlat_model_eisensteinQuotient
    (p : ℕ) [NeZero p] (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {T : Type*} [AddCommGroup T] (sp : JZero p →+ T)
    (hmodel : letI := heckeModuleBar p
      ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H),
        Module.Finite (GaloisRep.ratLocalizedAt ℓ) H ∧ Module.Flat (GaloisRep.ratLocalizedAt ℓ) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) ≃
            ↥(Submodule.torsionBy ℤ (EisensteinQuotient p (heckeModuleBar p)) ((ℓ : ℤ) ^ n)),
          (∀ f g, e (f * g) = e f + e g) ∧
          (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
              (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)),
            (∀ h : H, g h = σ (f h)) →
            ∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
                = (e f : EisensteinQuotient p (heckeModuleBar p)) →
              eisensteinQuotientMk p (heckeModuleBar p) (σ • x)
                = (e g : EisensteinQuotient p (heckeModuleBar p))) ∧
          (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
            ((ℓ : ℤ) ^ k) • (e f : EisensteinQuotient p (heckeModuleBar p)) = 0 →
            (∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
                = (e f : EisensteinQuotient p (heckeModuleBar p)) → sp x ∈ spKernelImage sp) →
            ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)
              (Coalgebra.counit h)) < 1)) :
    letI := heckeModuleBar p
    RaynaudFor ℓ sp := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_raynaudFor_of_le_finiteFlat_model_eisensteinQuotient.solution
