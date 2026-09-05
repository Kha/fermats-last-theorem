import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_modularFunctionFieldFull_algHom_ext
import P2M.Util
namespace P2MW.S_ModularCurve_IsFrickeAutFull_eq_frickeInvolutionFull

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution {N : ℕ} [NeZero N] {σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N} (hσ : IsFrickeAutFull N σ) : σ = frickeInvolutionFull N := by
  have hτ := ModularCurve.isFrickeAutFull_frickeInvolutionFull N ⟨σ, hσ⟩
  have h : (σ : modularFunctionFieldFull N →ₐ[ℚ] modularFunctionFieldFull N)
      = (frickeInvolutionFull N : modularFunctionFieldFull N →ₐ[ℚ] modularFunctionFieldFull N) := by
    refine ModularCurve.modularFunctionFieldFull_algHom_ext fun d hd hdN => ?_
    obtain ⟨e, hde⟩ := hdN
    haveI : NeZero e := ⟨fun he => NeZero.ne N (by rw [hde, he, mul_zero])⟩
    show σ ⟨qExpand ℚ d jq, _⟩ = frickeInvolutionFull N ⟨qExpand ℚ d jq, _⟩
    exact (hσ d e hde.symm hd inferInstance).trans (hτ d e hde.symm hd inferInstance).symm
  exact AlgEquiv.ext fun x => AlgHom.congr_fun h x

end
