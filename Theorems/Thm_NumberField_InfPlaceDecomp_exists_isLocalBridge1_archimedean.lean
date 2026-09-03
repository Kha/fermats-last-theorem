import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge
import P2M.Util
import P2M.Sol.S_NumberField_InfPlaceDecomp_exists_isLocalBridge1_archimedean
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean
    {p : ℕ} [Fact p.Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (πi : ↥archimedeanDecomposition →* ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ h : ↥archimedeanDecomposition,
      ((πi h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ))
    (hπbij : Function.Bijective πi)
    (hσF : σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup)
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    (α : Type) [Finite α] (eP : P ≅ Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α) (hB : ∀ b : B, p • b = 0)
    (κ : B →+ M →+ Additive (w.Completion)ˣ)
    (hκeq : ∀ (h : ↥archimedeanDecomposition) (b : B) (m : M),
      κ (B.ρ ((πi h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) m) =
        (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w).ρ (πi h) (κ b m))
    (hκ : ∀ c : B →+ Additive (w.Completion)ˣ, ∃! m : M, ∀ b, κ b m = c b) :
    ∃ Λ : (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype R ⟶ NumberField.InfPlaceDecomp.localUnits ℚ ↥F w) →+
        H1 (Rep.res archimedeanLoc M),
      IsLocalBridge₁ πi ((Rep.resFunctor (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (A := Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w))
        (AddMonoidHom.id (Additive (w.Completion)ˣ)) (M := Rep.res archimedeanLoc M) κ Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype P ⟶ NumberField.InfPlaceDecomp.localUnits ℚ ↥F w,
        (Rep.resFunctor (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype).map f ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M)) ∧
      (∀ y ∈ continuousH1 archimedeanLoc (Rep.res archimedeanLoc M), ∃ φ, Λ φ = y) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfPlaceDecomp_exists_isLocalBridge1_archimedean.solution
