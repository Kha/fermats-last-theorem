import Mathlib
import P2M.Util
import P2M.Sol.S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField

set_option autoImplicit false
theorem KummerTheory.algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField (K L : Type*) [Field K] [Field L]
    [Algebra K L] {n : ℕ} (S : Finset Kˣ)
    [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))]
    (σ : L ≃ₐ[K] L) (hσ : ∀ α : L, ∀ u ∈ S, α ^ n = algebraMap K L (u : K) → σ α = α) : σ = 1 := by p2m_exact_reverting @_root_.P2MW.S_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField.solution
