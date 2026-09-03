import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer

open scoped Pointwise

theorem Ideal.ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [Module.Finite A B] [Module.IsTorsionFree A B] [Module.Finite C B] [Module.IsTorsionFree C B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) (hp : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [IsGaloisGroup (MulAction.stabilizer G P) C B] :
    p.ramificationIdx' (P.under C) = 1 ∧ p.inertiaDeg' (P.under C) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer.solution
