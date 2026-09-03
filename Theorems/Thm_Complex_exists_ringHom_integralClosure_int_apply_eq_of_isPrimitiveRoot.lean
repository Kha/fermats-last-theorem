import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot

theorem Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ z : integralClosure ℤ ℂ,
        (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.solution
