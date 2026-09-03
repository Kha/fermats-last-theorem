import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift

set_option autoImplicit false

universe u

theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hup : ∀ n : ℕ, Module.Finite k (DoubleComplex.HTot
        ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n))
    (hrow : ∀ p : ℕ, Module.Finite k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N),
            (-1 : ℤ) ^ p * (Module.finrank k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot
            ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift.solution
