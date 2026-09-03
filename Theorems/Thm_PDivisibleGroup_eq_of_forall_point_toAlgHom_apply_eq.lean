import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
    (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
    {h : ℕ} (H : PDivisibleGroup O p h) (v : ℕ) (a b : H.level v)
    (hab : ∀ x : H.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.toAlgHom x a = PDivisibleGroup.Point.toAlgHom x b) :
    a = b := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq.solution
