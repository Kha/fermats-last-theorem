import Definitions.Def_TaylorWiles_Primes
import P2M.Util
namespace P2MW.S_Matrix_trace_pow_eq_sum_pow

theorem solution {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [Matrix.trace_one, one_add_one_eq_two]
    | 1 => simpa using htr
    | (k + 2) =>
      rw [Matrix.trace_pow_add_two, htr, hdet, ih (k + 1) (by omega), ih k (by omega)]
      ring
