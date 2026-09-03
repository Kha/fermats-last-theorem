import Mathlib.FieldTheory.RatFunc.AsPolynomial
import P2M.Util
import P2M.Sol.S_RatFunc_exists_algEquiv_apply_X_eq_moebius

theorem RatFunc.exists_algEquiv_apply_X_eq_moebius {K : Type*} [Field K] (a b c d : K) (hdet : a * d - b * c ≠ 0) : ∃ φ : RatFunc K ≃ₐ[K] RatFunc K, φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C d) := by p2m_exact_reverting @_root_.P2MW.S_RatFunc_exists_algEquiv_apply_X_eq_moebius.solution
