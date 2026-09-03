import Mathlib
import Theorems.Thm_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology

universe u

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C :=
  (f.isConstructible_image hC).mem_of_mem_closure_of_forall_specializes hy
    (by rintro _ ⟨c, hc, rfl⟩; exact hgen c hc)
