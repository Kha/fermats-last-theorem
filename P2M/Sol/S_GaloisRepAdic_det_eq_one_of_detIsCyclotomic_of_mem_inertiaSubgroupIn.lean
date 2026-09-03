import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
import P2M.Util
namespace P2MW.S_GaloisRepAdic_det_eq_one_of_detIsCyclotomic_of_mem_inertiaSubgroupIn

set_option autoImplicit false
open IsLocalRing

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (hdet : ρ.DetIsCyclotomic p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hp : p.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    LinearMap.det (ρ.ρ σ) = 1 := by

  have hmem : ∀ n : ℕ, LinearMap.det (ρ.ρ σ) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    intro n
    have hndvd : ¬ q ∣ p ^ n := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
    have hfix : ∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ (1 : ℕ) := fun μ hμ => by
      rw [pow_one]
      exact ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn hq P hP hσ hndvd hμ
    have h := hdet.2 n σ 1 hfix
    rw [Nat.cast_one] at h
    refine (Ideal.span_singleton_le_iff_mem _).2 ?_ h
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow hdet.1 n

  have hbot : (⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n) = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have : LinearMap.det (ρ.ρ σ) - 1 ∈ (⨅ n : ℕ, (IsLocalRing.maximalIdeal A) ^ n) := Ideal.mem_iInf.2 hmem
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
