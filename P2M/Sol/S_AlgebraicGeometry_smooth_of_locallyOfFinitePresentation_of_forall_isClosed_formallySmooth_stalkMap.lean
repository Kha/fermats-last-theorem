import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_smooth_of_locallyOfFinitePresentation_of_forall_isClosed_formallySmooth_stalkMap

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] [JacobsonSpace ↑X]
    (h : ∀ x : ↑X, IsClosed ({x} : Set ↑X) → (f.stalkMap x).hom.FormallySmooth) :
    Smooth f := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  have hne' : ((f.smoothLocus : Set ↑X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro htop
    exact hne (TopologicalSpace.Opens.ext htop)
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hne' (f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed)
  exact hx ((Scheme.Hom.mem_smoothLocus).mpr (h x hxc))
