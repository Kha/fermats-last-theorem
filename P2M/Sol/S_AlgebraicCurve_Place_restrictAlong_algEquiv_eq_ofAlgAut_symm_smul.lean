import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  show σ x ∈ v.toValuationSubring ↔ _
  rfl

#print axioms solution
