import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
    {X Y : Scheme.{u}} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
    (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : Scheme.{u}) ⟶ Y) :
    ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint.solution
