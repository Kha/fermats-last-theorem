import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range

theorem IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ Set.range (algebraMap F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.solution
