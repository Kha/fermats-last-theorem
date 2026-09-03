import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Place.ord_eq_mul_or_eq_mul_of_modular_support {K F : Type*} [Field K] [Field F] [Algebra K F] (U : Place K F) {p : ℕ} (hp : 0 < p) (Φ : Polynomial (Polynomial ℤ)) (hΦ₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1) (hΦ₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1) {x y : F} (hrel : Φ.eval₂ (eval₂RingHom (Int.castRingHom F) x) y = 0) (hx : U.ord x < 0) : U.ord y < 0 ∧ (U.ord x = p * U.ord y ∨ U.ord y = p * U.ord x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support.solution
