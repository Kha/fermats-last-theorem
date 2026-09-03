import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer

set_option autoImplicit false

universe u

open scoped Pointwise

theorem Ideal.ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
    [Algebra A C] [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A B] [Algebra B C] [IsScalarTower A B C] [Module.Finite B C] [Module.IsTorsionFree B C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G A C]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal C) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup ↥(MulAction.stabilizer G P) B C] :
    Ideal.ramificationIdx' p (P.under B) = 1 ∧ Ideal.inertiaDeg' p (P.under B) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer.solution
