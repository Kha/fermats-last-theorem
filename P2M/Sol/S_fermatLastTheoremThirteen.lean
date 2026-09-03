import Theorems.Thm_flt_regular
import Theorems.Thm_IsCyclotomicExtension_Rat_thirteen_pid
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Basic
import P2M.Util
namespace P2MW.S_fermatLastTheoremThirteen

open NumberField

set_option backward.isDefEq.respectTransparency false in
theorem solution : FermatLastTheoremFor 13 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine flt_regular (p := 13) ?_ (by norm_num)
  convert Nat.coprime_one_right _
  exact classNumber_eq_one_iff.2 (IsCyclotomicExtension.Rat.thirteen_pid (CyclotomicField 13 ℚ))
