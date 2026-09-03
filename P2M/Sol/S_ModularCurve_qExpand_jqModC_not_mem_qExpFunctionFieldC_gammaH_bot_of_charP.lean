import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash
import Theorems.Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S
import Theorems.Thm_ModularCurve_apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S
import Theorems.Thm_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC
import P2M.Util
namespace P2MW.S_ModularCurve_qExpand_jqModC_not_mem_qExpFunctionFieldC_gammaH_bot_of_charP
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

set_option autoImplicit false

open scoped MatrixGroups

namespace NonmemPen14

open CongruenceSubgroup in

theorem gammaH_bot_le_of_dvd {M M' : ℕ} [NeZero M] [NeZero M'] (h : M ∣ M') :
    CohCarrier.GammaH M' ⊥ ≤ CohCarrier.GammaH M ⊥ := by
  intro A hA
  obtain ⟨hA0, h1⟩ := CohCarrier.mem_GammaH_iff.mp hA
  rw [Subgroup.mem_bot] at h1
  have h11 : (((A : SL(2, ℤ)) 1 1 : ℤ) : ZMod M') = 1 := by
    have := congrArg (fun u : (ZMod M')ˣ => (u : ZMod M')) h1
    first | simpa using this | simpa [Gamma0Map] using this | (simp at this; exact this)
  have h10 : (((A : SL(2, ℤ)) 1 0 : ℤ) : ZMod M') = 0 := Gamma0_mem.mp hA0
  have hA0' : A ∈ Gamma0 M := by
    rw [Gamma0_mem]
    have := congrArg (ZMod.castHom h (ZMod M)) h10
    rwa [map_intCast, map_zero] at this
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  rw [Subgroup.mem_bot]
  ext
  have := congrArg (ZMod.castHom h (ZMod M)) h11
  rw [map_intCast, map_one] at this
  first | simpa using this | simpa [Gamma0Map] using this | (simp at this ⊢; exact this)

theorem gammaH_mono {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

end NonmemPen14

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (N d : ℕ) [NeZero N] [NeZero d] (hℓ : ¬ ℓ ∣ N * d) (hd : ¬ d ∣ N) :
    ModularCurve.qExpand K d (ModularCurve.jqModC K) ∉ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) := by
  intro hmem

  have hMK : ((N * d : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    exact hℓ
  haveI : NeZero ((N * d : ℕ) : K) := ⟨hMK⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ (N * d) := by
    have hdeg : (Polynomial.cyclotomic (N * d) K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos (N * d))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (N * d) K) hdeg
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
  obtain ⟨φ, -⟩ := Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot ℓ (N * d) hℓ K ζ hζ
  obtain ⟨Θ, hΘ⟩ :=
    ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash (N * d) ⊥ hℓ K φ
      ModularGroup.S

  have hle : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) ≤
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (N * d) ⊥) := by
    exact ModularCurve.qExpFunctionFieldC_mono K (NonmemPen14.gammaH_bot_le_of_dvd (dvd_mul_right N d))
  let x' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (N * d) ⊥) :=
    ⟨ModularCurve.qExpand K d (ModularCurve.jqModC K), hle hmem⟩
  obtain ⟨y, hy⟩ :=
    ModularCurve.exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S (N * d) hℓ K φ N d
      rfl Θ hΘ x' hmem
  have hval :=
    ModularCurve.apply_eq_qExpand_jqModC_of_coe_eq_qExpand_jqModC_of_cuspExpansion_S (N * d) hℓ K φ N d rfl Θ hΘ x' rfl
  exact hd (ModularCurve.dvd_of_qExpand_eq_qExpand_jqModC K d N y (hy.symm.trans hval))
