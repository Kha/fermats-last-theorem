import Mathlib
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (L : Type) [Field L] [NumberField L] (A : ValuationSubring L) (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hA : ∀ x : 𝓞 L, A.valuation (algebraMap (𝓞 L) L x) ≤ 1)
    (hQ : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (algebraMap (𝓞 L) L x) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal = Q ∧ A = (w.valuation L).valuationSubring := by
  classical

  have hRV : ∀ r : 𝓞 L, algebraMap (𝓞 L) L r ∈ A := fun r => (A.valuation_le_one_iff _).1 (hA r)

  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField L)
  have hAtop : A ≠ ⊤ := by
    intro htop
    obtain ⟨q, hqQ, hq0⟩ := Q.ne_bot_iff.1 hQ0
    have hlt : A.valuation (algebraMap (𝓞 L) L q) < 1 := (hQ q).1 hqQ
    have hq0' : (algebraMap (𝓞 L) L q) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hq0

    have hmem : (algebraMap (𝓞 L) L q)⁻¹ ∈ A := by rw [htop]; trivial
    have h1 : A.valuation (algebraMap (𝓞 L) L q)⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 hmem
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hq0'))] at h1
    exact absurd hlt (not_lt.2 h1)

  obtain ⟨w, hw, hcent⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem (R := 𝓞 L) (K := L) A hRV hAtop
  refine ⟨w, ?_, ?_⟩
  ·
    ext r
    rw [hcent r, ValuationSubring.mem_nonunits_iff, hQ r]
  · rw [hw, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
