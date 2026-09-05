module

public import Definitions.Def_ModularCurve_AtkinLehner
public import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_frickeInvolutionFull_apply_apply

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] (x : modularFunctionFieldFull N) : frickeInvolutionFull N (frickeInvolutionFull N x) = x := by
  by_cases h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ
  · have hσ := ModularCurve.isFrickeAutFull_frickeInvolutionFull N h
    have hc : (frickeInvolutionFull N : modularFunctionFieldFull N →ₐ[ℚ] modularFunctionFieldFull N).comp
          (frickeInvolutionFull N : modularFunctionFieldFull N →ₐ[ℚ] modularFunctionFieldFull N)
        = AlgHom.id ℚ (modularFunctionFieldFull N) := by
      refine ModularCurve.modularFunctionFieldFull_algHom_ext fun d hd hdN => ?_
      obtain ⟨e, hde⟩ := hdN
      haveI : NeZero e := ⟨fun he => NeZero.ne N (by rw [hde, he, mul_zero])⟩
      show frickeInvolutionFull N (frickeInvolutionFull N ⟨qExpand ℚ d jq, _⟩) = ⟨qExpand ℚ d jq, _⟩
      rw [hσ d e hde.symm hd inferInstance]
      exact hσ e d ((mul_comm e d).trans hde.symm) inferInstance hd
    exact AlgHom.congr_fun hc x
  · rw [ModularCurve.frickeInvolutionFull_eq_refl N h]
    rfl

end
