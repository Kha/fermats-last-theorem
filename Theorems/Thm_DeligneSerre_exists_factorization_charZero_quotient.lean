import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_factorization_charZero_quotient

theorem DeligneSerre.exists_factorization_charZero_quotient {T : Type*} [CommRing T] [Module.Finite ℤ T]
  [Module.IsTorsionFree ℤ T] {k : Type*} [Field k] (χ : T →+* k) :
  ∃ 𝔭 ∈ minimalPrimes T,
    𝔭 ≤ RingHom.ker χ ∧
      (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
        CharZero (T ⧸ 𝔭) ∧
          IsDomain (T ⧸ 𝔭) ∧
            Module.Finite ℤ (T ⧸ 𝔭) ∧ Algebra.IsIntegral ℤ (T ⧸ 𝔭) ∧ ∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_factorization_charZero_quotient.solution
