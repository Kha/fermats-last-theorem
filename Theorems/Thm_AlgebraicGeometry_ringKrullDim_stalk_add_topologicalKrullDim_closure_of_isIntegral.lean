import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral.solution
