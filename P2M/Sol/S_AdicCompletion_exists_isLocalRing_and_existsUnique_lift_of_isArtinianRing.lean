import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
import P2M.Util
namespace P2MW.S_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing

set_option autoImplicit false

open IsLocalRing

namespace COMPFAC

theorem apply_eq_zero_of_mem_map_pow {B T : Type} [CommRing B] [CommRing T] (𝔭 : Ideal B) (n : ℕ)
    (φ : B →+* T) (hφ : (𝔭 ^ n).map φ = ⊥)
    (χ : AdicCompletion 𝔭 B →+* T) (hχ : χ.comp (algebraMap B (AdicCompletion 𝔭 B)) = φ)
    {y : AdicCompletion 𝔭 B} (hy : y ∈ (𝔭 ^ n).map (algebraMap B (AdicCompletion 𝔭 B))) :
    χ y = 0 := by
  have h : χ y ∈ ((𝔭 ^ n).map (algebraMap B (AdicCompletion 𝔭 B))).map χ := Ideal.mem_map_of_mem χ hy
  rw [Ideal.map_map, hχ, hφ] at h
  simpa using h

end COMPFAC

theorem solution
    (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsMaximal] :
    ∃ (_ : IsLocalRing (AdicCompletion 𝔭 B)) (_ : IsNoetherianRing (AdicCompletion 𝔭 B))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion 𝔭 B)) (AdicCompletion 𝔭 B)),
      maximalIdeal (AdicCompletion 𝔭 B) = 𝔭.map (algebraMap B (AdicCompletion 𝔭 B)) ∧
      Function.Surjective ((residue (AdicCompletion 𝔭 B)).comp (algebraMap B (AdicCompletion 𝔭 B))) ∧
      RingHom.ker ((residue (AdicCompletion 𝔭 B)).comp (algebraMap B (AdicCompletion 𝔭 B))) = 𝔭 ∧
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] (φ : B →+* T),
        (∀ b ∈ 𝔭, φ b ∈ maximalIdeal T) →
        ∃! Φ : AdicCompletion 𝔭 B →+* T, IsLocalHom Φ ∧ Φ.comp (algebraMap B (AdicCompletion 𝔭 B)) = φ := by
  classical
  have hfg : 𝔭.FG := IsNoetherian.noetherian 𝔭
  obtain ⟨hN, hloc, hmax, hcomp, hcomap, hsurj⟩ :=
    AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal 𝔭
  refine ⟨hloc, hN, hcomp, hmax, hsurj, ?_, ?_⟩
  ·
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue]
    exact hcomap
  · intro T _ _ _ φ hφ

    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal T).mp ‹_›
    have hφle : 𝔭.map φ ≤ maximalIdeal T := Ideal.map_le_iff_le_comap.mpr fun b hb => hφ b hb
    have hφpow : (𝔭 ^ n).map φ = ⊥ := by
      rw [Ideal.map_pow]
      exact le_bot_iff.mp ((Ideal.pow_right_mono hφle n).trans (le_of_eq hn))
    have hker : ∀ b ∈ 𝔭 ^ n, φ b = 0 := fun b hb =>
      (Ideal.map_eq_bot_iff_le_ker φ).mp hφpow hb

    let ψ : B ⧸ 𝔭 ^ n →+* T := Ideal.Quotient.lift (𝔭 ^ n) φ hker
    let Φ : AdicCompletion 𝔭 B →+* T := ψ.comp (AdicCompletion.evalₐ 𝔭 n).toRingHom
    have hΦcomp : Φ.comp (algebraMap B (AdicCompletion 𝔭 B)) = φ := by
      ext b
      simp only [Φ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        AdicCompletion.evalₐ_algebraMap, Ideal.Quotient.lift_mk]
    have hΦloc : IsLocalHom Φ := by
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hmem : a ∈ maximalIdeal (AdicCompletion 𝔭 B) := (mem_maximalIdeal a).mpr hna
      rw [hmax] at hmem
      have h2 : Φ a ∈ (𝔭.map (algebraMap B (AdicCompletion 𝔭 B))).map Φ := Ideal.mem_map_of_mem Φ hmem
      rw [Ideal.map_map, hΦcomp] at h2
      exact (mem_maximalIdeal _).mp (hφle h2) ha
    refine ⟨Φ, ⟨hΦloc, hΦcomp⟩, ?_⟩
    rintro Ψ ⟨-, hΨcomp⟩
    ext x
    obtain ⟨b, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add 𝔭 hfg n x
    rw [map_add, map_add, COMPFAC.apply_eq_zero_of_mem_map_pow 𝔭 n φ hφpow Ψ hΨcomp hy,
      COMPFAC.apply_eq_zero_of_mem_map_pow 𝔭 n φ hφpow Φ hΦcomp hy,
      ← RingHom.comp_apply Ψ, ← RingHom.comp_apply Φ, hΨcomp, hΦcomp]
