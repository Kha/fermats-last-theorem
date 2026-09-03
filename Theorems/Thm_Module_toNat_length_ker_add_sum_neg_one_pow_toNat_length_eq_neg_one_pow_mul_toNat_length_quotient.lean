import Mathlib
import P2M.Util
import P2M.Sol.S_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (g : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = g)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, g < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (N : ℕ)
    (htors0 : ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ z : LinearMap.ker (δ 0), a • z = 0)
    (htors : ∀ (i : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ N,
      ∀ q : LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype, a • q = 0)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIN : IsLocalRing.maximalIdeal R ^ N ≤ I)
    (hU : Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.ker ((δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1)
    (hW : ∀ (J' : Ideal R) (hJ' : J' ≤ IsLocalRing.maximalIdeal R), (∃ N : ℕ, IsLocalRing.maximalIdeal R ^ N ≤ J') →
      ((∀ z : (R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] K 0, (δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R) z = 0 →
          ∃ w : (R ⧸ J') ⊗[R] K 0, (δ 0).baseChange (R ⧸ J') w = 0 ∧
            LinearMap.rTensor (K 0) (Submodule.factor hJ') w = z) ↔ I ≤ J')) :
    ((Module.length R (LinearMap.ker (δ 0))).toNat : ℤ) +
        ∑ i ∈ Finset.range g, (-1) ^ (i + 1) *
          ((Module.length R (LinearMap.ker (δ (i + 1)) ⧸
            (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype)).toNat : ℤ) =
      (-1) ^ g * ((Module.length R (R ⧸ I)).toNat : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_Module_toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient.solution
