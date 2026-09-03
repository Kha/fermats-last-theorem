import Theorems.Thm_AlgEquiv_apply_eq_inv_of_pow_eq_one
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import P2M.Util
namespace P2MW.S_WeierstrassCurve_det_galoisRep_eq_neg_one_of_mul_self_eq_one
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y
attribute [-simp] WeierstrassCurve.Affine.placeOf_asIdeal

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [CharZero K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} (hp : p.Prime) (c : K ≃ₐ[F] K) (hc : c * c = 1) (hc1 : c ≠ 1) : LinearMap.det (galoisRepModuleEnd F W p c) = -1 := by
  haveI : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have h1 := WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one W hp (NeZero.ne _) c ζ
    hζ.pow_eq_one
  have h2 := AlgEquiv.apply_eq_inv_of_pow_eq_one c hc hc1 hp.ne_zero hζ.pow_eq_one
  set d := LinearMap.det ((DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W⁄K).Point p)
    c).toZModLinearMap p) with hd
  have hdet : LinearMap.det (galoisRepModuleEnd F W p c) = d :=
    congrArg LinearMap.det (LinearMap.ext fun _ => rfl)
  have h3 : ζ ^ (d.val + 1) = 1 := by
    rw [pow_succ, ← h1, h2, inv_mul_cancel₀ (hζ.ne_zero hp.ne_zero)]
  have h4 : ((d.val + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr ((hζ.pow_eq_one_iff_dvd _).mp h3)
  rw [Nat.cast_succ, ZMod.natCast_zmod_val] at h4
  rw [hdet]
  exact eq_neg_of_add_eq_zero_left h4
