import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory open AlgebraicGeometry hiding exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] :
    ∃ (V : (X N₀ p).Opens) (d : ℕ), Flat (π₂.1 ∣_ V) ∧ LocallyOfFinitePresentation (π₂.1 ∣_ V) ∧
      (∀ y : V, (π₂.1 ∣_ V).finrank y = d) ∧
      ∀ x : X N₀ p, ringKrullDim ((X N₀ p).presheaf.stalk x) ≤ 1 → x ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one.solution
