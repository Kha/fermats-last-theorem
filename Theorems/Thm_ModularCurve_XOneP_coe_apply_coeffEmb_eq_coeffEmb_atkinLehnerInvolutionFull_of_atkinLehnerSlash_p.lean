import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_coe_apply_coeffEmb_eq_coeffEmb_atkinLehnerInvolutionFull_of_atkinLehnerSlash_p
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.XOneP.coe_apply_coeffEmb_eq_coeffEmb_atkinLehnerInvolutionFull_of_atkinLehnerSlash_p
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : 5 ≤ M)
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hτ :
      (∀ (e : ℕ) [NeZero e], e ∣ M →
        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq) →
          ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq)) ∧
        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq) →
          ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq)))) :

        (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
          (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
          ((τ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((ModularCurve.atkinLehnerInvolutionFull M p f :
              ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_coe_apply_coeffEmb_eq_coeffEmb_atkinLehnerInvolutionFull_of_atkinLehnerSlash_p.solution
