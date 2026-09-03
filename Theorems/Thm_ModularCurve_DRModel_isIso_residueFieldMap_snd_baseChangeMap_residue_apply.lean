import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModel_isIso_residueFieldMap_snd_baseChangeMap_residue_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.isIso_residueFieldMap_snd_baseChangeMap_residue_apply (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsLocalRing O]
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    IsIso ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).residueFieldMap
      ((DRModel.baseChangeMap (IsLocalRing.residue O)).base
        (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModel_isIso_residueFieldMap_snd_baseChangeMap_residue_apply.solution
