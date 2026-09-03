import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import P2M.Util
namespace P2MW.S_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) :
    addOrderOf (reduceHom hΔ P) = N := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← hP, addOrderOf_nsmul_eq_zero, map_zero]
  · rw [← hP]
    apply addOrderOf_dvd_of_nsmul_eq_zero
    refine WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ hN ?_ (smul_zero _) ?_
    · rw [smul_comm, ← hP, addOrderOf_nsmul_eq_zero, smul_zero]
    · rw [map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
