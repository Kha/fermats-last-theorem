import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
namespace P2MW.S_ModularCurve_eisensteinNumerator_coprime

open ModularCurve

theorem solution (p : ℕ) (hp : p ≠ 0) : (eisensteinNumerator p).Coprime p := by
  refine Nat.Coprime.coprime_dvd_left (eisensteinNumerator_dvd p) ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.succ_sub_one, Nat.succ_eq_add_one]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)
