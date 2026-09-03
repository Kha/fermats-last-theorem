import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable

set_option autoImplicit false

universe u v

theorem Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1) [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Algebra.IsUnramifiedAt R P := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable.solution
