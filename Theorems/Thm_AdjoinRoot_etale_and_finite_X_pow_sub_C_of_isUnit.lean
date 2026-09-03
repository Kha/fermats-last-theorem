import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit

set_option autoImplicit false

universe u

open Polynomial

theorem AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit
    {R : Type u} [CommRing R] (n : ℕ) (u : R) (hn : IsUnit (n : R)) (hu : IsUnit u) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.solution
