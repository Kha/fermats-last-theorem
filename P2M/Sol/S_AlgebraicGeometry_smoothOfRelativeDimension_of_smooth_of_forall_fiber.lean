import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x

  obtain ⟨m, hm⟩ : ∃ m : ℕ, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    letI := (f.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hstd
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

  obtain ⟨U', V', hV', hxV', e', hm'⟩ :=
    AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField f x m U hU V hV hxV e hm
  have hmn : m = n :=
    AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
      (f.fiberToSpecResidueField (f.base x)) n (h (f.base x)) m U' V' hV' (f.asFiber x) hxV' e' hm'
  subst hmn
  exact ⟨U, hU, V, hV, hxV, e, hm⟩
