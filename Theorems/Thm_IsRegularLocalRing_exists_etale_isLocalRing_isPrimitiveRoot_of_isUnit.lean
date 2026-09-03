import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_etale_isLocalRing_isPrimitiveRoot_of_isUnit

set_option autoImplicit false

open IsLocalRing Polynomial

universe u

theorem IsRegularLocalRing.exists_etale_isLocalRing_isPrimitiveRoot_of_isUnit
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsRegularLocalRing R') (_ : IsDomain R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Module.Free R R') (_ : FaithfulSMul R R') (_ : Algebra.Etale R R')
      (_ : IsAdicComplete (maximalIdeal R') R') (ζ : R'),
      IsPrimitiveRoot ζ e ∧ ringKrullDim R' = 2 ∧
        maximalIdeal R' = Ideal.span {algebraMap R R' ϖ, algebraMap R R' s} := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_etale_isLocalRing_isPrimitiveRoot_of_isUnit.solution
