import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_card_smul_eq_zero_of_tateH0
import Theorems.Thm_Rep_nonempty_tateCohomology_dimShiftUpObj_iso
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_dimShiftDownObj
import P2M.Util
namespace P2MW.S_Rep_card_smul_eq_zero_of_tateCohomology
attribute [-simp] Rep.coe_tateδneg2_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ) (x : A.tateCohomology q) : (Fintype.card G : k) • x = 0 := by
  induction q using Int.induction_on generalizing A with
  | zero => exact Rep.card_smul_eq_zero_of_tateH0 A x
  | succ i ih =>
    obtain ⟨e⟩ := Rep.nonempty_tateCohomology_dimShiftUpObj_iso A (i : ℤ)
    rw [← e.toLinearEquiv.apply_symm_apply x, ← map_smul, ih, map_zero]
  | pred i ih =>
    obtain ⟨e⟩ := Rep.nonempty_tateCohomology_iso_dimShiftDownObj A (-(i : ℤ) - 1)
    have h : (-(i : ℤ) - 1 + 1) = -(i : ℤ) := by ring
    rw [h] at e
    rw [← e.toLinearEquiv.symm_apply_apply x, ← map_smul, ih, map_zero]
