import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module_and_exists_presentation_isFrameOn
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData) (hI : I.IsInvertible) :
    Scheme.Modules.IsInvertible I.module ∧
    ∃ (φ : ∀ V : X.Opens, Γ(I.module, V) →+ (X.functionField : Type u)),
      (∀ (V V' : X.Opens) (h : V' ≤ V), Nonempty V' → ∀ m : Γ(I.module, V), φ V' (I.module.presheaf.map (homOfLE h).op m) = φ V m) ∧
      (∀ (V : X.Opens) [Nonempty V] (a : Γ(X, V)) (m : Γ(I.module, V)), φ V (a • m) = algebraMap Γ(X, V) X.functionField a * φ V m) ∧
      (∀ V : X.Opens, Nonempty V → Function.Injective (φ V)) ∧
      (∀ (W : X.affineOpens) (hW : Nonempty (W : X.Opens)) (g : Γ(X, W)), g ∈ nonZeroDivisors Γ(X, W) → I.ideal W = Ideal.span {g} →
        ∃ m : Γ(I.module, (W : X.Opens)), Scheme.Modules.IsFrameOn m W ∧
          φ W m = (letI := hW; X.germToFunctionField (W : X.Opens) g)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn.solution
