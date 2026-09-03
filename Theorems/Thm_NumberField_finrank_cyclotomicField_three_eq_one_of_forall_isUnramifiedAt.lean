import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import P2M.Util
import P2M.Sol.S_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
set_option autoImplicit false
open scoped NumberField
theorem NumberField.finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    Module.finrank (CyclotomicField 3 ℚ) F = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt.solution
