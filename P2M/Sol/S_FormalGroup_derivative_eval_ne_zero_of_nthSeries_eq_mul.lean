import Mathlib
import Theorems.Thm_FormalGroup_exists_isUnit_derivative_nthSeries_eq_natCast_mul
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
namespace P2MW.S_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (hqV : (q : V) ≠ 0) (G : FormalGroup V) [G.IsComm]
    (P : Polynomial V) (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = (P : PowerSeries V) * U)
    (r : V) (hr : r ∈ maximalIdeal V) (hPr : P.eval r = 0) :
    (Polynomial.derivative P).eval r ≠ 0 := by
  obtain ⟨u, hu, hd⟩ := FormalGroup.exists_isUnit_derivative_nthSeries_eq_natCast_mul G q
  obtain ⟨e, -, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal V) r hr

  rw [hq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, PowerSeries.derivative_coe] at hd
  have h := congrArg e hd
  rw [map_add, map_mul, map_mul, map_mul, hep, hep, hPr, zero_mul, _root_.zero_add, map_natCast] at h

  intro h0
  rw [h0, mul_zero] at h
  exact (mul_ne_zero hqV (hu.map e).ne_zero) h.symm
