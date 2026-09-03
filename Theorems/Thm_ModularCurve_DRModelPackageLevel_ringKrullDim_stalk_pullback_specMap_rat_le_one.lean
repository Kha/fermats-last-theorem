import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (y : ↥(pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ringKrullDim ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one.solution
