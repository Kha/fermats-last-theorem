import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : SemilinearAut K F) (v : AlgebraicCurve.Place K F)
    (hv : v.IsRational) (hσv : (σ • v).IsRational) (f : F) :
    (σ • v).evalAt (σ • f) = SemilinearAut.baseAut σ (v.evalAt f) := by
  classical
  by_cases hf : f ∈ v.toValuationSubring
  ·
    have hσf : σ • f ∈ (σ • v).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring]
      exact ValuationSubring.smul_mem_pointwise_smul σ f v.toValuationSubring hf
    apply (σ • v).algebraMap_residueField_injective
    rw [(σ • v).algebraMap_evalAt hσv hσf, ← SemilinearAut.smulResidueRingEquiv_algebraMap σ v,
      v.algebraMap_evalAt hv hf]

    show residue _ _ = IsLocalRing.ResidueField.mapEquiv _ (residue _ _)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  ·
    have hσf : σ • f ∉ (σ • v).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hf
    rw [Place.evalAt, Place.evalAt, dif_neg hσf, dif_neg hf, map_zero]
