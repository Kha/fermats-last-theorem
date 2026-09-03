import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite
universe u in

theorem AlgebraicGeometry.map_appTop_mem_nonZeroDivisors_of_flat
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Flat f]
    (r : R) (hr : r ∈ nonZeroDivisors R) (U : Y.Opens) (hU : IsAffineOpen U) :
    Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      ∈ nonZeroDivisors Γ(Y, U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat.solution
