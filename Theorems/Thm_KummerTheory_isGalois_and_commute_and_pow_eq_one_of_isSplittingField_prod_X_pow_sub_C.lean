import Mathlib
import P2M.Util
import P2M.Sol.S_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C

set_option autoImplicit false
theorem KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C
    (K L : Type*) [Field K] [Field L] [Algebra K L] {n : ℕ} (hμ : (primitiveRoots n K).Nonempty)
    (S : Finset Kˣ) [Polynomial.IsSplittingField K L (∏ u ∈ S, (Polynomial.X ^ n - Polynomial.C ((u : Kˣ) : K)))] :
    IsGalois K L ∧ (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧ ∀ σ : L ≃ₐ[K] L, σ ^ n = 1 := by p2m_exact_reverting @_root_.P2MW.S_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C.solution
