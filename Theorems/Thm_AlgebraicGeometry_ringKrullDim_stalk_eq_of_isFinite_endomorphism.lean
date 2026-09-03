import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [IsFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism.solution
