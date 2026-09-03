import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_AlgebraicCurve_traceDiff_apply
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Differential_traceAlong_eq_traceDiff

set_option autoImplicit false

open AlgebraicCurve KaehlerDifferential TensorProduct

theorem solution
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : AlgebraicCurve.SeparableAlong K φ) (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.traceAlong φ η =
      (letI := AlgebraicCurve.algebraAlong φ
       haveI := AlgebraicCurve.isScalarTower_along φ
       AlgebraicCurve.traceDiff K F F' η) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Algebra.IsSeparable F F' := h
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'

  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
  | tmul y ω =>

    have he : KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F' (y ⊗ₜ ω) =
        y • Differential.pullbackAlong φ ω := by
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [he, Differential.traceAlong_smul_pullbackAlong φ h y ω]
    show Algebra.trace F F' y • ω = traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω)
    rw [traceDiff_apply]
  | add s t hs ht =>
    rw [map_add, map_add, map_add, hs, ht]
