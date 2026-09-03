import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_CuspForm_exists_GammaH_coe_eq_alSlash
attribute [-instance] CuspForm.GammaH_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_GammaH_coe_eq_alSlash
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (F : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑F := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_GammaH_coe_eq_alSlash.solution
