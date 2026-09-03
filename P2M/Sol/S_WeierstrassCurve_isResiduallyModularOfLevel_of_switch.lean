import Mathlib
import Definitions.Def_WeierstrassCurve_ModularityProps
import P2M.Util
namespace P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_switch

open WeierstrassCurve

theorem solution {W W' : WeierstrassCurve ℤ} {N : ℕ}
    (hmod : W'.IsModularModelOfLevel N)
    (hND : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W'.Δ → ℓ ∣ N)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
      (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)) :
    W.IsResiduallyModularOfLevel 5 N := by
  obtain ⟨f, hf, hap⟩ := hmod
  obtain ⟨𝔪, h𝔪max, h𝔪p⟩ :=
    FLTPrelim.exists_maximalIdeal_natCast_prime_mem (p := 5) (by norm_num)
  refine ⟨f, 𝔪, hf, h𝔪max, h𝔪p, ?_⟩
  intro ℓ hℓ hgood hℓN hℓ5
  have hgood' : W'.IsGoodPrimeFor ℓ := fun hdvd => hℓN (hND ℓ hℓ hdvd)
  refine ⟨((W'.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ), ?_, ?_⟩
  · rw [hap ℓ hℓ hgood' hℓN]
    push_cast
    rfl
  · obtain ⟨k, hk⟩ := hcong ℓ hℓ hgood hgood' hℓ5
    have hcast : ((W'.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ)
        - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ)
        = ((5 : ℕ) : integralClosure ℤ ℂ) * ((k : ℤ) : integralClosure ℤ ℂ) := by
      rw [← Int.cast_sub, hk]
      push_cast
      ring
    rw [hcast]
    exact Ideal.mul_mem_right _ _ h𝔪p
