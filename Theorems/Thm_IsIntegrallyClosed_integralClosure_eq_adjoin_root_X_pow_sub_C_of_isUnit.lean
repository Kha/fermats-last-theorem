import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit

set_option autoImplicit false

open Polynomial

theorem IsIntegrallyClosed.integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (n : ℕ) (u : A) (hn : IsUnit (n : A)) (hu : IsUnit u) :
    integralClosure A (AdjoinRoot (X ^ n - C (algebraMap A K u) : K[X])) =
      Algebra.adjoin A {AdjoinRoot.root (X ^ n - C (algebraMap A K u) : K[X])} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit.solution
