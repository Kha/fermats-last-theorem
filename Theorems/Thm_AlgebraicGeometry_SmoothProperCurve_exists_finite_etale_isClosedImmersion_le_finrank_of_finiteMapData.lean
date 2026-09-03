import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) (N : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀)
      (B : Type u) (_ : CommRing B) (_ : Algebra R₀ B) (_ : Module.Finite R₀ B) (_ : Algebra.Etale R₀ B)
      (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c R₀ = specMap R₀ B ∧ N ≤ Module.finrank R₀ B := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData.solution
