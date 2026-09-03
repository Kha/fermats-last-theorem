import Mathlib
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_charZero_eigenvector_of_residual_character

theorem DeligneSerre.exists_charZero_eigenvector_of_residual_character {T : Type*} [CommRing T] [Module.Finite ℤ T]
  [Module.IsTorsionFree ℤ T] {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M]
  {k : Type*} [Field k] (χ : T →+* k) :
  ∃ 𝔭 ∈ minimalPrimes T,
    𝔭 ≤ RingHom.ker χ ∧
      (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
        CharZero (T ⧸ 𝔭) ∧
          (∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ) ∧
            ∃ x : M,
              x ≠ 0 ∧
                (∀ p ∈ 𝔭, p • x = 0) ∧
                  (∀ (r : T), r • x = 0 → r ∈ 𝔭) ∧
                    ∀ (h h' : T), (Ideal.Quotient.mk 𝔭) h = (Ideal.Quotient.mk 𝔭) h' → h • x = h' • x := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_charZero_eigenvector_of_residual_character.solution
