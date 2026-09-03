import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_denseRange_of_isAlgClosed

theorem RingHom.denseRange_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (σ : F →+* ℂ) :
    DenseRange σ := by p2m_exact_reverting @_root_.P2MW.S_RingHom_denseRange_of_isAlgClosed.solution
