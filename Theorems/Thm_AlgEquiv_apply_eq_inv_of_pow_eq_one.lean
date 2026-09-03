import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgEquiv_apply_eq_inv_of_pow_eq_one

theorem AlgEquiv.apply_eq_inv_of_pow_eq_one {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [CharZero K] (c : K ≃ₐ[F] K) (hc : c * c = 1) (hc1 : c ≠ 1) {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : c ζ = ζ⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AlgEquiv_apply_eq_inv_of_pow_eq_one.solution
