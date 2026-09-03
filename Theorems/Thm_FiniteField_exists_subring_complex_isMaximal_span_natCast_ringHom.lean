import Mathlib
import P2M.Util
import P2M.Sol.S_FiniteField_exists_subring_complex_isMaximal_span_natCast_ringHom

set_option autoImplicit false

theorem FiniteField.exists_subring_complex_isMaximal_span_natCast_ringHom
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [CharP k p] :
    ∃ (A : Subring ℂ) (_ : (Ideal.span ({(p : A)} : Set A)).IsMaximal),
      Nonempty (k →+* A ⧸ Ideal.span ({(p : A)} : Set A)) := by p2m_exact_reverting @_root_.P2MW.S_FiniteField_exists_subring_complex_isMaximal_span_natCast_ringHom.solution
