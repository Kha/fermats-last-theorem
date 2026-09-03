import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    (x₁ x₂ : ↥(fibre0 (N₀ := N₀) toκ)) (h₁ : IsClosed ({x₁} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h₂ : IsClosed ({x₂} : Set ↥(fibre0 (N₀ := N₀) toκ)))
    (h : (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₁ = (𝔓.comp κ toκ 1 ≫ fibreMap0 𝔓.π toκ).base x₂) :
    x₁ = x₂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_eq_of_isClosed_of_comp_one_fibreMap0_pi_apply_eq.solution
