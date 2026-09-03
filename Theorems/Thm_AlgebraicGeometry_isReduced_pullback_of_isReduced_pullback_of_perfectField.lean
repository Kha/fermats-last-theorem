import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_pullback_of_isReduced_pullback_of_perfectField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {κ₀ : Type u} [Field κ₀] [PerfectField κ₀] (x₀ : Spec (CommRingCat.of κ₀) ⟶ S)
    [IsReduced (pullback f x₀)]
    {k : Type u} [Field k] (ι : κ₀ →+* k) (x : Spec (CommRingCat.of k) ⟶ S)
    (hx : x = Spec.map (CommRingCat.ofHom ι) ≫ x₀) :
    IsReduced (pullback f x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField.solution
