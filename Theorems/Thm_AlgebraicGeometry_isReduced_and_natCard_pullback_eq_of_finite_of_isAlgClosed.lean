import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k₀))
    [LocallyOfFiniteType z] [IsReduced Z] [Finite ↥Z]
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k) :
    IsReduced (pullback z (Spec.map (CommRingCat.ofHom ι))) ∧
      Nat.card ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) = Nat.card ↥Z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.solution
