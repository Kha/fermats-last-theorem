import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (πi : ↥archimedeanDecomposition →* ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ h : ↥archimedeanDecomposition,
      ((πi h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ))
    (hπbij : Function.Bijective πi)
    (hσF : σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup) :

    (∀ s : ↥archimedeanDecomposition, archimedeanLoc s ∈ F.fixingSubgroup → s = 1) ∧

    (∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.Completion)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (w.Completion)ˣ, ∀ v : V, ψ (f v) = φ v) ∧

    (∀ (α : Type) [Finite α]
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype
          (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)))),
      ∃ χ : (ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj
          (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)),
        (groupCohomology.d₀₁ _).hom χ = (u : ↥archimedeanDecomposition → _)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean.solution
