import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (h₁ : (Scheme.Modules.pullback i₁).map σ = 0) (h₂ : (Scheme.Modules.pullback i₂).map σ = 0) :
    σ = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced.solution
