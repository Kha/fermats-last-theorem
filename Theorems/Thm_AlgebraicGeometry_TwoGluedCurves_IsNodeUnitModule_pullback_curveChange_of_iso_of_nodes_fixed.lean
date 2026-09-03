import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_curveChange_of_iso_of_nodes_fixed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves

universe u v

theorem AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.pullback_curveChange_of_iso_of_nodes_fixed
    {κ : Type u} [Field κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (ws : X ≅ X) (hws : ws.hom ≫ x = x)
    (α₁ : C₁ ≅ C₁) (hα₁ : α₁.hom ≫ c₁ = c₁) (hα₁i : α₁.hom ≫ i₁.1 = i₁.1 ≫ ws.hom)
    (α₂ : C₂ ≅ C₂) (hα₂ : α₂.hom ≫ c₂ = c₂) (hα₂i : α₂.hom ≫ i₂.1 = i₂.1 ≫ ws.hom)
    (hα₁p : ∀ j, (p₁ j).1 ≫ α₁.hom = (p₁ j).1) (hα₂p : ∀ j, (p₂ j).1 ≫ α₂.hom = (p₂ j).1)
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) (u : ι → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules)
    (hM : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M) :
    IsNodeUnitModule x i₁ i₂ p₁ p₂ h u
      ((Scheme.Modules.pullback (curveChange (c := x) (c' := x) ws.hom hws h)).obj M) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_curveChange_of_iso_of_nodes_fixed.solution
