import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field

set_option autoImplicit false

theorem Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] :
    ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field.solution
