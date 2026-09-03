import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import P2M.Util
namespace P2MW.S_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul

set_option autoImplicit false

theorem solution
    {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (ϖ : D) (hϖ : ϖ ≠ 0)
    (Q₁ : Ideal D) [Q₁.IsPrime]
    (G H u : D) (e : ℕ) (hH : ¬ IsUnit H) (hHQ₁ : H ∉ Q₁)
    (hu : IsUnit u) (hGH : G * H = ϖ ^ e * u) :
    ∃ Q : Ideal D, Q.IsPrime ∧ Q.height = 1 ∧ ϖ ∈ Q ∧ Q ≠ Q₁ := by
  classical
  by_contra hcon

  have hall : ∀ (Q : Ideal D), Q.IsPrime → Q.height = 1 → ϖ ∈ Q → Q = Q₁ :=
    fun Q hQ hh hm => by_contra fun hne => hcon ⟨Q, hQ, hh, hm, hne⟩

  let K := FractionRing D
  have hϖe : algebraMap D K (ϖ ^ e) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D K)).mpr (pow_ne_zero e hϖ)
  obtain ⟨G', hG'⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one K
    (algebraMap D K G / algebraMap D K (ϖ ^ e)) (by
      intro p hp hp1
      by_cases hmem : ϖ ∈ p
      ·
        have hpQ : p = Q₁ := hall p hp hp1 hmem
        refine ⟨u, H, ?_, ?_⟩
        · rw [hpQ]; exact hHQ₁
        · rw [div_mul_eq_mul_div, ← map_mul, hGH, map_mul, mul_div_cancel_left₀ _ hϖe]
      ·
        exact ⟨G, ϖ ^ e, fun h => hmem (hp.mem_of_pow_mem e h), div_mul_cancel₀ _ hϖe⟩)

  have hGe : G = ϖ ^ e * G' := by
    apply IsFractionRing.injective D K
    rw [map_mul, hG', mul_comm]
    exact (div_mul_cancel₀ _ hϖe).symm

  have hGH' : G' * H = u := by
    apply mul_left_cancel₀ (pow_ne_zero e hϖ)
    rw [← hGH, hGe]
    ring
  have hGHu : IsUnit (G' * H) := by rw [hGH']; exact hu
  exact hH (isUnit_of_mul_isUnit_right hGHu)
