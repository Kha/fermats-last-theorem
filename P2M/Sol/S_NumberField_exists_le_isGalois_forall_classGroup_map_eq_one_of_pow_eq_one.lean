import Mathlib
import Theorems.Thm_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
namespace P2MW.S_NumberField_exists_le_isGalois_forall_classGroup_map_eq_one_of_pow_eq_one
attribute [-instance] NumberField.LevelArith.instCommGroupUnitsModPow
attribute [-simp] groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk

set_option autoImplicit false
open NumberField ExtCitation
open scoped nonZeroDivisors

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] (hF : F.IsUnramifiedOutside S) :
    ∃ (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'') (_ : NumberField ↥F''),
      F''.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F'' ∧
      ∀ (φ : ClassGroup (𝓞 ↥F) →* ClassGroup (𝓞 ↥F''))
        (_ : ∀ (I : (Ideal (𝓞 ↥F))⁰) (J : (Ideal (𝓞 ↥F''))⁰),
          (J : Ideal (𝓞 ↥F'')) = (I : Ideal (𝓞 ↥F)).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) →
          φ (ClassGroup.mk0 I) = ClassGroup.mk0 J)
        (c : ClassGroup (𝓞 ↥F)), (∃ k : ℕ, c ^ p ^ k = 1) → φ c = 1 := by
  classical
  obtain ⟨F'', h, hfd, hF'', hgal, hcap⟩ :=
    NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal S hpS F hF
  haveI := hfd
  haveI : NumberField ↥F'' := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  refine ⟨F'', h, inferInstance, hF'', hgal, fun φ hφ c hc => ?_⟩
  obtain ⟨k, hck⟩ := hc

  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c

  have hIk : ClassGroup.mk0 (I ^ p ^ k) = 1 := by rw [map_pow, hck]
  have hprin : ((I ^ p ^ k : (Ideal (𝓞 ↥F))⁰) : Ideal (𝓞 ↥F)).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (I ^ p ^ k).2).mp hIk
  have hIne : ((I : (Ideal (𝓞 ↥F))⁰) : Ideal (𝓞 ↥F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 ↥F, ((I : Ideal (𝓞 ↥F)) ^ p ^ k) = Ideal.span {a} := by
    refine ⟨hprin.generator, ?_⟩
    rw [← SubmonoidClass.coe_pow]
    exact (Ideal.span_singleton_generator _).symm
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at ha
    exact pow_ne_zero _ hIne ha

  have hJprin := hcap (I : Ideal (𝓞 ↥F)) k a ha0 ha

  have hinj : Function.Injective (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) := by
    intro x y hxy
    apply RingOfIntegers.coe_injective
    apply (IntermediateField.inclusion h).injective
    have := congrArg (fun z : 𝓞 ↥F'' => (z : ↥F'')) hxy
    exact this
  have hJne : (I : Ideal (𝓞 ↥F)).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact hIne
  let J : (Ideal (𝓞 ↥F''))⁰ := ⟨_, mem_nonZeroDivisors_of_ne_zero hJne⟩
  rw [hφ I J rfl]
  exact (ClassGroup.mk0_eq_one_iff J.2).mpr hJprin
