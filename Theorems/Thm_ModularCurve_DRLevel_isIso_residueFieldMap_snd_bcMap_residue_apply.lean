import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRLevel.isIso_residueFieldMap_snd_bcMap_residue_apply
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsIso ((DRLevel.XO.toBase (N₀ := N₀) ρO).residueFieldMap
      ((DRLevel.bcMap ρO (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply.solution
