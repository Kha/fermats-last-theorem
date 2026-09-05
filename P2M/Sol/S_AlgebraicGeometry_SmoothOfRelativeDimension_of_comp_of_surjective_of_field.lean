import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {G Q : Scheme.{u}} [Nonempty G] (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
    (g h : ℕ) [SmoothOfRelativeDimension g (q ≫ fQ)] [SmoothOfRelativeDimension h q] [Surjective q]
    [QuasiCompact q] : SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by
  haveI : Smooth q := SmoothOfRelativeDimension.smooth h q
  haveI : Smooth (q ≫ fQ) := SmoothOfRelativeDimension.smooth g (q ≫ fQ)
  haveI : Smooth fQ := AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective q fQ
  exact AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective q fQ g h

