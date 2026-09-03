import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_lineBundle
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (t : (𝔉.twoAffineOpenCover.cover c).A01ˣ) :
    Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle.solution
