import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
    (F : OModulePresheaf c) (𝒱 : X.TwoAffineOpenCover) :
    F.CechFinite 𝒱.toOrderedAffineCover ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff.solution
