import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable.solution
