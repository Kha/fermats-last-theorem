import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_succ
import P2M.Util
namespace P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_add

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (principalUnits R (k + n)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) ^ n := by
  induction n with
  | zero => rw [add_zero, pow_zero, Subgroup.relIndex_self]
  | succ n ih =>
    rw [pow_succ, ← ih, ← add_assoc,
      ← IsDiscreteValuationRing.relIndex_principalUnits_succ (R := R) (k := k + n) (by omega), mul_comm]
    exact (Subgroup.relIndex_mul_relIndex _ _ _
      (principalUnits_antitone (Nat.le_succ _)) (principalUnits_antitone (Nat.le_add_right k n))).symm
