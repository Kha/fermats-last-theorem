import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_iso_invModule_tensor_module_of_pullback_tensor_invModule_iso_invModule_of_isIso
attribute [-simp] AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.nonempty_iso_invModule_tensor_module_of_pullback_tensor_invModule_iso_invModule_of_isIso
    {X' X : Scheme.{u}} (π : X' ⟶ X) [IsIso π] (ℒ : X.Modules) (I₁ I₂ : X.IdealSheafData) (J₁ J₂ : X'.IdealSheafData)
    (hJ₁ : I₁.comap π = J₁) (hJ₂ : I₂.comap π = J₂) (hJ₁i : J₁.IsInvertible) (hJ₂i : J₂.IsInvertible)
    (e : Nonempty ((Scheme.Modules.pullback π).obj ℒ ⊗ J₂.invModule ≅ J₁.invModule)) :
    I₁.IsInvertible ∧ I₂.IsInvertible ∧ Nonempty (ℒ ≅ I₁.invModule ⊗ I₂.module) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_iso_invModule_tensor_module_of_pullback_tensor_invModule_iso_invModule_of_isIso.solution
