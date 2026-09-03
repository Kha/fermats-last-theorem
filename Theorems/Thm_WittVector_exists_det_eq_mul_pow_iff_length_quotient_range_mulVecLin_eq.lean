import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq

set_option autoImplicit false

open scoped PadicInt Padic

theorem WittVector.exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (c : ℤ_[p] →+* WittVector p K) (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]) (h : ℕ) :
    (∃ u : ℤ_[p]ˣ, γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h) ↔
      Module.length (WittVector p K)
        ((Fin 2 → WittVector p K) ⧸ LinearMap.range (Matrix.mulVecLin (γ.map c))) = h := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_det_eq_mul_pow_iff_length_quotient_range_mulVecLin_eq.solution
