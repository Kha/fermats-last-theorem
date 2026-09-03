import Theorems.Thm_flt_regular
import Theorems.Thm_IsCyclotomicExtension_Rat_eleven_pid
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Basic
import P2M.Util
namespace P2MW.S_fermatLastTheoremEleven

open NumberField

set_option backward.isDefEq.respectTransparency false in
theorem solution : FermatLastTheoremFor 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine flt_regular (p := 11) ?_ (by norm_num)
  convert Nat.coprime_one_right _
  exact classNumber_eq_one_iff.2 (IsCyclotomicExtension.Rat.eleven_pid (CyclotomicField 11 ℚ))
