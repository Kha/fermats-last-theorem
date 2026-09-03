import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ 𝔉' : SmoothProperCurve.FiniteMapData (baseChange R c R') (sectionBaseChange R' ε),
      𝔉'.U = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ∧ 𝔉'.V = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ∧
        𝔉'.m = 𝔉.m ∧
        (IsLocalRing R → Module.Finite R R' → 𝔉.LevelSetsGenericallyEtale → 𝔉'.LevelSetsGenericallyEtale) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.solution
