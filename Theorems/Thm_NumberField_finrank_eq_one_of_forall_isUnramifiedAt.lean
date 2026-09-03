import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import P2M.Util
import P2M.Sol.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt

open scoped NumberField in
theorem NumberField.finrank_eq_one_of_forall_isUnramifiedAt
    (K : Type*) [Field K] [NumberField K]
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.solution
