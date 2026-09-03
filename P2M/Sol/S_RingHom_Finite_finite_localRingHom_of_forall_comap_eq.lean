import Mathlib
import P2M.Util
namespace P2MW.S_RingHom_Finite_finite_localRingHom_of_forall_comap_eq

set_option autoImplicit false

theorem solution
    {B C : Type*} [CommRing B] [CommRing C] (φ : B →+* C) (hφ : φ.Finite)
    (𝔮 : Ideal C) [𝔮.IsPrime]
    (huniq : ∀ Q : Ideal C, Q.IsPrime → Q.comap φ = 𝔮.comap φ → Q = 𝔮) :
    (Localization.localRingHom (𝔮.comap φ) 𝔮 φ rfl).Finite := by
  classical
  letI : Algebra B C := φ.toAlgebra
  haveI : Module.Finite B C := hφ

  set 𝔭 : Ideal B := 𝔮.comap φ with h𝔭
  let M' : Submonoid C := 𝔭.primeCompl.map (algebraMap B C)
  let C' := Localization M'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) C' := Localization.isLocalization

  letI algRC' : Algebra (Localization.AtPrime 𝔭) C' :=
    (IsLocalization.map C' (algebraMap B C) 𝔭.primeCompl.le_comap_map : Localization.AtPrime 𝔭 →+* C').toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime 𝔭) C' := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    show algebraMap B C' = (IsLocalization.map C' (algebraMap B C) 𝔭.primeCompl.le_comap_map).comp (algebraMap B _)
    rw [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq B C C']
  haveI hfinC' : Module.Finite (Localization.AtPrime 𝔭) C' := Module.Finite.of_isLocalization B C 𝔭.primeCompl
  haveI : Algebra.IsIntegral (Localization.AtPrime 𝔭) C' := Algebra.IsIntegral.of_finite _ _

  have hunit : ∀ n ∈ 𝔮.primeCompl, IsUnit (algebraMap C C' n) := by
    intro n hn
    by_contra hnu
    obtain ⟨𝔫, h𝔫max, hn𝔫⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)

    have h1 : (𝔫.comap (algebraMap (Localization.AtPrime 𝔭) C')) = IsLocalRing.maximalIdeal _ := by
      haveI : (𝔫.comap (algebraMap (Localization.AtPrime 𝔭) C')).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
      exact IsLocalRing.eq_maximalIdeal inferInstance
    have h2 : (𝔫.comap (algebraMap C C')).comap φ = 𝔭 := by
      have : (𝔫.comap (algebraMap C C')).comap φ = (𝔫.comap (algebraMap (Localization.AtPrime 𝔭) C')).comap
          (algebraMap B (Localization.AtPrime 𝔭)) := by
        rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq B (Localization.AtPrime 𝔭) C']
        rfl
      rw [this, h1]
      exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime 𝔭) 𝔭
    haveI : (𝔫.comap (algebraMap C C')).IsPrime := Ideal.IsPrime.comap _
    have h3 := huniq _ this h2
    have : n ∈ 𝔮 := by rw [← h3]; exact hn𝔫
    exact hn this

  haveI : IsLocalization.AtPrime C' 𝔮 :=
    IsLocalization.of_le M' 𝔮.primeCompl (by
      rintro _ ⟨b, hb, rfl⟩
      exact fun h => hb (by exact h)) hunit
  let e : C' ≃ₐ[C] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔮.primeCompl C' (Localization.AtPrime 𝔮)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.primeCompl) (Localization.AtPrime 𝔮) :=
    IsLocalization.isLocalization_of_algEquiv M' e

  letI algRS : Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) :=
    (Localization.localRingHom 𝔭 𝔮 φ rfl).toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) := by
    refine IsScalarTower.of_algebraMap_eq (fun b => ?_)
    show algebraMap B (Localization.AtPrime 𝔮) b = Localization.localRingHom 𝔭 𝔮 φ rfl (algebraMap B _ b)
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B C (Localization.AtPrime 𝔮)]
    rfl
  have : Module.Finite (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮) :=
    Module.Finite.of_isLocalization B C 𝔭.primeCompl
  exact this
