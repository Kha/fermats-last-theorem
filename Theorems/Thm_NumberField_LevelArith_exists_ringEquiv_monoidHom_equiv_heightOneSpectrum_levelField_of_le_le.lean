import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup
attribute [-simp] groupCohomology.locTotal₂S_apply groupCohomology.continuousH2ToH2_mk groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.locTotal_apply groupCohomology.totalPairing_apply

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open IsDedekindDomain NumberField NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le
    (L L₁ F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F : L₁ ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L₁ ↥(levelField L₁ F hL₁F)] :
    ∃ (θ : ↥(levelField L₁ F hL₁F) ≃+* ↥(levelField L F hLF))
      (ι : (↥(levelField L₁ F hL₁F) ≃ₐ[↥L₁] ↥(levelField L₁ F hL₁F)) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)))
      (e : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F)) ≃
        IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L F hLF))),
      (∀ x : ↥(levelField L₁ F hL₁F), ((θ x : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) ∧
      Function.Injective ι ∧
      (∀ (σ : ↥(levelField L₁ F hL₁F) ≃ₐ[↥L₁] ↥(levelField L₁ F hL₁F)) (x : ↥(levelField L F hLF)), ι σ x = θ (σ (θ.symm x))) ∧
      (∀ τ : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF),
        τ ∈ ι.range ↔ ∀ y : ↥L₁, τ (θ (algebraMap ↥L₁ ↥(levelField L₁ F hL₁F) y)) = θ (algebraMap ↥L₁ ↥(levelField L₁ F hL₁F) y)) ∧
      ι.range.index = Module.finrank ↥L ↥(levelField L L₁ hLL₁) ∧
      (∀ γ : ↥L₁.fixingSubgroup, ι (levelGal L₁ F hL₁F γ) =
        levelGal L F hLF ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL₁ γ.2⟩) ∧
      ι.range = (L₁.fixingSubgroup.comap L.fixingSubgroup.subtype).map (levelGal L F hLF) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (x : 𝓞 ↥(levelField L₁ F hL₁F)),
        NumberField.RingOfIntegers.mapRingEquiv θ x ∈ (e w₁).asIdeal ↔ x ∈ w₁.asIdeal) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (x : ↥(levelField L₁ F hL₁F)),
        (e w₁).valuation ↥(levelField L F hLF) (θ x) = w₁.valuation ↥(levelField L₁ F hL₁F) x) ∧
      (∀ w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F)),
        (NumberField.PlaceDecomp.decomp ↥L₁ ↥(levelField L₁ F hL₁F) w₁).map ι =
          ι.range ⊓ NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (e w₁)) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (S : Set Nat.Primes),
        w₁ ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L₁ F hL₁F) S ↔
          e w₁ ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F hLF) S) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le.solution
