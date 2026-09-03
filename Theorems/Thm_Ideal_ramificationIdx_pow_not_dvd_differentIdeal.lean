import Mathlib.RingTheory.DedekindDomain.Different
import P2M.Util
import P2M.Sol.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal

theorem Ideal.ramificationIdx_pow_not_dvd_differentIdeal (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [@Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B))]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((Ideal.ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ Ideal.ramificationIdx' p P ∣ differentIdeal A B := by p2m_exact_reverting @_root_.P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.solution
