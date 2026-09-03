import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_nonempty_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.IsNodeUnitModule.nonempty_iso
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
    {M₁ M₂ : CurveModel κ (RatFunc κ)} {i₁ : M₁.C ⟶ X} {i₂ : M₂.C ⟶ X}
    {hi₁ : i₁ ≫ x = M₁.toBase} {hi₂ : i₂ ≫ x = M₂.toBase}
    {s : ℕ} {a b : Fin s → κˣ}
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : Fin s → Γ(T, ⊤)ˣ} {M M' : (pullback x h).Modules}
    (hM : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M)
    (hM' : IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u M') :
    Nonempty (M ≅ M') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_nonempty_iso.solution
