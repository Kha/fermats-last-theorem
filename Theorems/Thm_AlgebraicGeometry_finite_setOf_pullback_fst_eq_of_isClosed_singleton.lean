import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    (z : X) (hz : IsClosed ({z} : Set X)) :
    {w : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) |
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) w = z}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton.solution
