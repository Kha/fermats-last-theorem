import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.exists_restrict_twist_of_isPullback_model_of_comp_eq
    {A : Type u} [CommRing A] (R₀ : Type u) [CommRing R₀] [Algebra A R₀] (k : Type u) [CommRing k] [Algebra A k] [Algebra R₀ k]
    [IsScalarTower A R₀ k]
    {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of A))
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ specMap R₀ k = specMap R₀ k)
    (F : pullback cX (specMap A k) ⟶ pullback cX (specMap A k))
    (hF₁ : F ≫ pullback.fst cX (specMap A k) = pullback.fst cX (specMap A k))
    (hF₂ : F ≫ pullback.snd cX (specMap A k) = pullback.snd cX (specMap A k) ≫ φ)
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (i : SchemeHomOver c (baseChange A cX k))
    {Cₚ : Scheme.{u}} (cₚ : Cₚ ⟶ Spec (CommRingCat.of R₀)) (iₚ : Cₚ ⟶ pullback cX (specMap A R₀)) (g : C ⟶ Cₚ)
    (hg : IsPullback g c cₚ (specMap R₀ k))
    (hgi : g ≫ iₚ ≫ pullback.fst cX (specMap A R₀) = i.1 ≫ pullback.fst cX (specMap A k)) :
    ∃ F_C : C ⟶ C,
      F_C ≫ i.1 = i.1 ≫ F ∧ F_C ≫ g = g ∧ IsPullback F_C c c φ ∧
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c, ∃ x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c,
        x'.1 ≫ F_C = φ ≫ x.1 ∧
        x'.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) = φ ≫ x.1 ≫ i.1 ≫ pullback.fst cX (specMap A k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_restrict_twist_of_isPullback_model_of_comp_eq.solution
