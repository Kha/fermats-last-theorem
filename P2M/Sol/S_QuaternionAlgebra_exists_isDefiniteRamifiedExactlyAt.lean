import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two
import Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three
import Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
import Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution (q : ℕ) (hq : q.Prime) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q := by
  rcases hq.eq_two_or_odd' with rfl | hodd
  · exact ⟨-1, -1, QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_one_two⟩
  · have h8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
      rcases hodd with ⟨k, rfl⟩
      omega
    rcases h8 with h | h | h | h
    · exact QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_of_mod_eight_eq_one q hq h
    · exact ⟨-1, -(q : ℚ), QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three q hq (by omega)⟩
    · exact ⟨-2, -(q : ℚ), QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five q hq h⟩
    · exact ⟨-1, -(q : ℚ), QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three q hq (by omega)⟩
