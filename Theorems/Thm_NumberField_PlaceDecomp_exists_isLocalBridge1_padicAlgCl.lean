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
import P2M.Sol.S_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπsurj : Function.Surjective π)
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    (α : Type) [Finite α] (eP : P ≅ Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α) (hB : ∀ b : B, p • b = 0)
    (κ : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκeq : ∀ (τ : primeLocalGaloisGroup q) (b : B) (m : M),
      κ (B.ρ ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (primeLocalToGlobal q τ) m) =
        (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (κ b m))
    (hκ : ∀ c : B →+ Additive (PadicAlgCl q)ˣ, ∃! m : M, ∀ b, κ b m = c b) :
    ∃ Λ : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κ Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
        (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl.solution
