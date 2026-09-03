import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_mem_forall_mem_range_of_isOpen

theorem RingHom.exists_mem_forall_mem_range_of_isOpen {n : ℕ} {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ b ∈ U, ∀ j, b j ∈ Set.range σ := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_mem_forall_mem_range_of_isOpen.solution
