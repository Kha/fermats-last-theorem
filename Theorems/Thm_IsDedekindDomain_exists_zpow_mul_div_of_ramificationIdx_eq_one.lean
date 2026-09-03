import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one

set_option autoImplicit false

universe u

open scoped Pointwise

theorem IsDedekindDomain.exists_zpow_mul_div_of_ramificationIdx_eq_one
    {A : Type u} {B : Type u} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (π : A) (p : Ideal A) [p.IsMaximal] (hp : p = Ideal.span {π})
    (q : Ideal B) [q.IsMaximal] (hq : q ≠ ⊥) (hpq : Ideal.map (algebraMap A B) p ≤ q)
    (he : Ideal.ramificationIdx' p q = 1)
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
    (z : L) (hz : z ≠ 0) :
    ∃ (n : ℤ) (b s : B), b ∉ q ∧ s ∉ q ∧
      z * (algebraMap B L s) = (algebraMap A L π) ^ n * algebraMap B L b := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one.solution
