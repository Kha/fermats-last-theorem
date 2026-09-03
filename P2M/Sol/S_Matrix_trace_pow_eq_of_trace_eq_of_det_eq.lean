import Definitions.Def_TaylorWiles_Primes
import P2M.Util
namespace P2MW.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq

theorem solution {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simpa using htr
    | (k + 2) =>
      rw [Matrix.trace_pow_add_two, Matrix.trace_pow_add_two, htr, hdet,
        ih (k + 1) (by omega), ih k (by omega)]
