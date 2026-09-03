import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_mem_range_of_pow_eq_one

theorem RingHom.mem_range_of_pow_eq_one {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ σ.range := by p2m_exact_reverting @_root_.P2MW.S_RingHom_mem_range_of_pow_eq_one.solution
