import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq
    {k K : Type u} [Field k] [IsAlgClosed k] [Field K] (ι : k →+* K)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = Spec.map (CommRingCat.ofHom ι))
    (x : ↥X) (hx : IsClosed ({x} : Set ↥X)) (hpx : p.base (IsLocalRing.closedPoint K) = x) :
    p = Spec.map (CommRingCat.ofHom ι) ≫ AlgebraicGeometry.pointOfClosedPoint f x hx := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_specMap_comp_pointOfClosedPoint_of_apply_closedPoint_eq.solution
