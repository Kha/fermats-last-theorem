import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.ClassNumber
import P2M.Util
import P2M.Sol.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub
set_option autoImplicit false
namespace NumberField
open scoped NumberField nonZeroDivisors
theorem exists_isBigO_card_absNorm_le_mk_eq_sub
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    ∃ (θ : ℝ) (_hθ : θ < 1), (fun x : ℝ =>
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x
          ∧ ClassGroup.mk0 I = c} : ℝ)
          - (dedekindZeta_residue K / classNumber K) * x)
      =O[Filter.atTop] fun x => x ^ θ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.solution
