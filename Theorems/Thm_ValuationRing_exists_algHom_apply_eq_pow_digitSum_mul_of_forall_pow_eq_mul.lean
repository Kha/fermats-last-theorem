import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.BigOperators.Fin
import P2M.Util
import P2M.Sol.S_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul

universe u v

theorem ValuationRing.exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
    {R : Type u} [CommRing R] {p : ℕ} (hunif : Irreducible (p : R))
    {S : Type v} [CommRing S] [IsDomain S] [ValuationRing S] [Algebra R S]
    (hpS : algebraMap R S p ∈ IsLocalRing.maximalIdeal S) (hp0 : algebraMap R S p ≠ 0)
    (σ : S →ₐ[R] S) (hσ : ∀ y : S, σ y - y ∈ IsLocalRing.maximalIdeal S)
    {r : ℕ} [NeZero r] (δ : Fin r → R) (hδ : ∀ i, δ i ∣ (p : R))
    (x : Fin r → S) (hx : ∀ i, x i ^ p = algebraMap R S (δ i) * x (i + 1))
    (π' : S) (hπ' : π' ^ (p ^ r - 1) = algebraMap R S p) :
    ∃ n : Fin r → ℕ, (∀ i, n i ≤ 1) ∧ (∀ i, Associated (δ i) ((p : R) ^ n i)) ∧
      ∃ t : S, t ^ (p ^ r - 1) = 1 ∧ σ π' = t * π' ∧
        ∀ i, σ (x i) = t ^ (∑ j : Fin r, n (i + j) * p ^ (r - 1 - (j : ℕ))) * x i := by p2m_exact_reverting @_root_.P2MW.S_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul.solution
