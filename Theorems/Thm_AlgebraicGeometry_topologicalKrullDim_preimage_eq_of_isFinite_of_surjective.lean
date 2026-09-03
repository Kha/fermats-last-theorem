import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.KrullDimension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (p : X ⟶ Y) (hp : p ≫ g = f) [IsFinite p] [Surjective p]
    (s : ↥(Spec (CommRingCat.of k))) :
    topologicalKrullDim ↥(g.base ⁻¹' {s}) = topologicalKrullDim ↥(f.base ⁻¹' {s}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective.solution
