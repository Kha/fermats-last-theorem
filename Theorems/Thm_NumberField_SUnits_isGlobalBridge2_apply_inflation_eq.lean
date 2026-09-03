import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.isGlobalBridge2_apply_inflation_eq
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F'] [IsGalois ℚ ↥F']
    (hFF' : F ≤ F') (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S)
    (π : (↥F' ≃ₐ[ℚ] ↥F') →* (↥F ≃ₐ[ℚ] ↥F))
    (hπ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F' σ) = AlgEquiv.restrictNormalHom ↥F σ)

    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {R' P' : Rep ℤ (↥F' ≃ₐ[ℚ] ↥F')} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res π B)
    (hf' : Function.Injective f'.hom) (hfg' : Function.Exact f'.hom g'.hom) (hg' : Function.Surjective g'.hom)
    [Module.Finite ℤ P] [Module.Finite ℤ P'] (hB : ∀ b : B, p • b = 0)
    (ρR : R' ⟶ Rep.res π R) (ρP : P' ⟶ Rep.res π P)
    (hρf : f' ≫ ρP = ρR ≫ (Rep.resFunctor π).map f) (hρg : g' = ρP ≫ (Rep.resFunctor π).map g)

    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (ιE' : NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE' : ∀ x, Additive.toMul (ιE' x) = Units.map (algebraMap ↥F' (AlgebraicClosure ℚ) : ↥F' →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F' Sℚ x))
    (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)
    (hjE : ∀ x, ιE' (jE.hom x) = ιE x)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {ΛE : H1 ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {ΛE' : H1 ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)) →+ continuousH2S S M}
    (hΛE' : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F') f' g' (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE'
      (show Rep.res π B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) ΛE')

    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (a' : cocycles₁ ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)))
    (ha' : ∀ (d' : (↥F' ≃ₐ[ℚ] ↥F')) (x' : R'),
      LinearMap.toAddMonoidHom ((a' : _ → _) d') x' = jE.hom (LinearMap.toAddMonoidHom ((a : _ → _) (π d')) (ρR.hom x'))) :
    ΛE' ((H1π _).hom a') = ΛE ((H1π _).hom a) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq.solution
