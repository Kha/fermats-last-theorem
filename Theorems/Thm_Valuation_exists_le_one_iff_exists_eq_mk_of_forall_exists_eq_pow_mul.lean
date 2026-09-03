import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Localization.FractionRing
import P2M.Util
import P2M.Sol.S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul

set_option autoImplicit false

open WithZero

theorem Valuation.exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
    (M : Type) [CommRing M] [IsDomain M] (K : Type) [Field K] (φ : M →+* K) (t : M) (ht0 : t ≠ 0) (ht : φ t = 0)
    (hfac : ∀ F : M, F ≠ 0 → ∃ (n : ℕ) (G : M), F = t ^ n * G ∧ φ G ≠ 0) :
    ∃ v : Valuation (FractionRing M) ℤᵐ⁰,
      (∀ x : FractionRing M, v x ≤ 1 ↔
        ∃ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 ∧ x = Localization.mk a ⟨b, hb⟩) ∧
      (∀ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (v (Localization.mk a ⟨b, hb⟩ : FractionRing M) < 1 ↔ φ a = 0)) ∧
      v (algebraMap M (FractionRing M) t) = exp (-1) ∧
      ∃ ψ : ↥v.valuationSubring →+* K, ∀ (x : ↥v.valuationSubring) (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (x : FractionRing M) = Localization.mk a ⟨b, hb⟩ → ψ x = φ a / φ b := by p2m_exact_reverting @_root_.P2MW.S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul.solution
