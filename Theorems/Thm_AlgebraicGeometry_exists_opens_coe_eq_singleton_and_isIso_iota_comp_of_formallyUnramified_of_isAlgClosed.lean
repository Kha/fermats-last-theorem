import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [FormallyUnramified q] (x : H) :
    ∃ U : H.Opens, (U : Set H) = {x} ∧ IsIso (U.ι ≫ q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_formallyUnramified_of_isAlgClosed.solution
