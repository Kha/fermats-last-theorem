import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_ModularCurve_JZeroTateModule
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import P2M.Util
namespace P2MW.S_DrinfeldCurve_exists_linearEquiv_rationalTateModule_baseChange_comp_eq

set_option autoImplicit false

open scoped TensorProduct

private theorem cancelBaseChange_comp_baseChange_baseChange {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [AddCommGroup M] [Module R M]
    (f : Module.End R M) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap ∘ₗ (f.baseChange A).baseChange B =
      f.baseChange B ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap := by
  rw [LinearMap.baseChange_baseChange]
  refine LinearMap.ext fun z => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

open DrinfeldCurve in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (E' : Type*) [Field E'] [Algebra ℚ_[ℓ] E'] [Algebra E E']
    [IsScalarTower ℚ_[ℓ] E E'] :
    let ρE : Representation E (hSubgroup q)
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
      (Module.End.baseChangeHom ℚ_[ℓ] E
          (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
        Module.End ℚ_[ℓ]
            (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
          Module.End E (E ⊗[ℚ_[ℓ]]
            ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
        ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
            (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))
    let ρE' : Representation E' (hSubgroup q)
        (E' ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
      (Module.End.baseChangeHom ℚ_[ℓ] E'
          (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
        Module.End ℚ_[ℓ]
            (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
          Module.End E' (E' ⊗[ℚ_[ℓ]]
            ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
        ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
            (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))
    ∃ e : (E' ⊗[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) ≃ₗ[E']
        (E' ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))),
      ∀ h : hSubgroup q, e.toLinearMap ∘ₗ (ρE h).baseChange E' = ρE' h ∘ₗ e.toLinearMap := by
  intro ρE ρE'
  exact ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ_[ℓ] E E' E' _,
    fun _ => cancelBaseChange_comp_baseChange_baseChange _⟩
