import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
set_option autoImplicit false
open CategoryTheory NumberField IsDedekindDomain ExtCitation

theorem NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x)) :
    ∀ φ : R →+ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ,
      ∃ ψ : (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)),
        (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ιE (φ x)) ∧
        ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₂.IsUnramifiedOutside S ∧
          ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup →
            ∀ x : P, (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective.solution
