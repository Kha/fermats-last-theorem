import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (s₀ : Spec (CommRingCat.of k₀) ⟶ Spec (CommRingCat.of R))
    (h₀ : ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k₀)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k₀))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s₀)) (i₂ : SchemeHomOver c₂ (pullback.snd c s₀))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s₀), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
            (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) =
          ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀)) \
            connectedComponentIn ((pullback.fst c s₀ ⁻¹ᵁ U : (pullback c s₀).Opens) : Set ↥(pullback c s₀))
              (((sectionFibrePoint ε s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        (∃ W₁ : (pullback c s₀).Opens, (W₁ : Set ↥(pullback c s₀)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s₀).Opens, (W₂ : Set ↥(pullback c s₀)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)))
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hs : s = Spec.map (CommRingCat.ofHom ι) ≫ s₀) :
    ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed.solution
