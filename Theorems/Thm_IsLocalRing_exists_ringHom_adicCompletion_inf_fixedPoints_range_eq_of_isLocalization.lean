import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)

    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (hBGnoeth : IsNoetherianRing ↥BG)
    (hfin : ∀ (hle : BG ≤ B), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥B)

    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

    (H : Subgroup (K ≃ₐ[k] K)) (hH : ∀ σ : K ≃ₐ[k] K, σ ∈ H ↔ σ ∈ G ∧ ∀ f : K, f ∈ Õ ↔ σ f ∈ Õ)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) :
    ∃ (_ : IsNoetherianRing ↥Õ) (_ : IsLocalRing ↥O₀) (_ : IsNoetherianRing ↥O₀) (hle : O₀ ≤ Õ)
      (act : ↥H → (AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ))
      (κ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),

      (∀ f : ↥O₀, IsUnit f ↔ IsUnit (Subring.inclusion hle f)) ∧

      (∀ (σ : ↥H) (f : ↥Õ), ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ,
        act σ (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) ∧
      (∀ (σ : ↥H) (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (act σ x) = 0) ∧
      (∀ (σ : ↥H) (F : AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        (∀ f : ↥Õ, ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ, F (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) →
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
          AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (F x) = 0) → F = act σ) ∧

      Function.Injective κ ∧
      (∀ f : ↥O₀, κ (algebraMap ↥O₀ _ f) = algebraMap ↥Õ _ (Subring.inclusion hle f)) ∧
      (∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, x ∈ Set.range κ ↔ ∀ σ : ↥H, act σ x = x) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization.solution
