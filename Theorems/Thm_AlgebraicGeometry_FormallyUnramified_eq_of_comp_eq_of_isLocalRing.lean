import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_isLocalRing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (a b : Spec (CommRingCat.of O) ⟶ X) (hf : a ≫ f = b ≫ f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of O))
    (ht : IsLocalRing.closedPoint O ∈ Set.range t.base)
    (hab : t ≫ a = t ≫ b) : a = b := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing.solution
