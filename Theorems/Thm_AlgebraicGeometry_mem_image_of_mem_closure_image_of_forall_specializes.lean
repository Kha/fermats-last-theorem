import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

universe u

theorem AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes.solution
