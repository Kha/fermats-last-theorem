import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow

set_option autoImplicit false

open Polynomial

theorem IsIntegrallyClosed.integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow
    {B F : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    (k : ℕ) (hk : IsUnit (k : B)) (v : B) (hv : IsUnit v) (h : F) (hh : h ≠ 0) (g : F)
    (hg : g = algebraMap B F v * h ^ k) :
    integralClosure B (AdjoinRoot (X ^ k - C g : F[X])) =
        Algebra.adjoin B {algebraMap F (AdjoinRoot (X ^ k - C g : F[X])) h⁻¹ * AdjoinRoot.root (X ^ k - C g : F[X])} ∧
      Algebra.Etale B (integralClosure B (AdjoinRoot (X ^ k - C g : F[X]))) ∧
      Module.Finite B (integralClosure B (AdjoinRoot (X ^ k - C g : F[X]))) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow.solution
