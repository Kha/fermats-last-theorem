import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_IsAbsolutelyIrreducible_of_isEquiv

set_option autoImplicit false
open scoped TensorProduct

theorem solution
    {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ρ₁.IsEquiv ρ₂) (h : ρ₁.IsAbsolutelyIrreducible) :
    ρ₂.IsAbsolutelyIrreducible := by
  classical
  obtain ⟨e⟩ := e
  let E : (ρ₁.baseChange (AlgebraicClosure k)).V ≃ₗ[AlgebraicClosure k] (ρ₂.baseChange (AlgebraicClosure k)).V :=
    e.toLinearEquiv.baseChange k (AlgebraicClosure k) ρ₁.V ρ₂.V
  have hE : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : (ρ₁.baseChange (AlgebraicClosure k)).V),
      E ((ρ₁.baseChange (AlgebraicClosure k)).ρ σ x) = (ρ₂.baseChange (AlgebraicClosure k)).ρ σ (E x) := by
    intro σ x
    show e.toLinearEquiv.baseChange k (AlgebraicClosure k) ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange (AlgebraicClosure k) x) =
      (ρ₂.ρ σ).baseChange (AlgebraicClosure k) (e.toLinearEquiv.baseChange k (AlgebraicClosure k) ρ₁.V ρ₂.V x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, e.map_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hE' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : (ρ₂.baseChange (AlgebraicClosure k)).V),
      E.symm ((ρ₂.baseChange (AlgebraicClosure k)).ρ σ y) = (ρ₁.baseChange (AlgebraicClosure k)).ρ σ (E.symm y) := by
    intro σ y
    apply E.injective
    rw [hE, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  intro W hW
  have hW' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ W.map (E.symm : _ →ₗ[AlgebraicClosure k] _),
      (ρ₁.baseChange (AlgebraicClosure k)).ρ σ x ∈ W.map (E.symm : _ →ₗ[AlgebraicClosure k] _) := by
    rintro σ _ ⟨y, hy, rfl⟩
    exact ⟨(ρ₂.baseChange (AlgebraicClosure k)).ρ σ y, hW σ y hy, hE' σ y⟩
  rcases h (W.map (E.symm : _ →ₗ[AlgebraicClosure k] _)) hW' with h0 | h1
  · left
    apply (Submodule.orderIsoMapComap E.symm).injective
    rw [map_bot]
    exact h0
  · right
    apply (Submodule.orderIsoMapComap E.symm).injective
    rw [map_top]
    exact h1
