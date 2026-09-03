import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.topologicalKrullDim_eq_of_iso_opens
    {k : Type u} [Field k] {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] [IsIntegral X] [IsIntegral Y]
    (U : X.Opens) (U' : Y.Opens) (hU : (U : Set X).Nonempty) (e : (U : Scheme.{u}) ≅ (U' : Scheme.{u})) :
    topologicalKrullDim ↥X = topologicalKrullDim ↥Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_of_iso_opens.solution
