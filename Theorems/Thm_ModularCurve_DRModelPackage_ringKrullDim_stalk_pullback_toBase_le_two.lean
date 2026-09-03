import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.ringKrullDim_stalk_pullback_toBase_le_two
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) :
    ringKrullDim ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk z) ≤ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two.solution
