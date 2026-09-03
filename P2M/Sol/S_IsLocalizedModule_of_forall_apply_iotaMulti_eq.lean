import Mathlib
import Theorems.Thm_exteriorPower_exists_linearEquiv_baseChange
import P2M.Util
namespace P2MW.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq

set_option autoImplicit false

open scoped TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (F : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hF : ∀ m : Fin n → M, F (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i => f (m i))) :
    IsLocalizedModule S F := by
  classical
  have hf : IsBaseChange A f := (isLocalizedModule_iff_isBaseChange S A f).mp inferInstance
  rw [isLocalizedModule_iff_isBaseChange S A]

  obtain ⟨e₁, he₁⟩ := exteriorPower.exists_linearEquiv_baseChange R A M n

  let g : A ⊗[R] M ≃ₗ[A] N := hf.equiv
  let e₂ : ⋀[A]^n (A ⊗[R] M) ≃ₗ[A] ⋀[A]^n N :=
    LinearEquiv.ofLinear (exteriorPower.map n g.toLinearMap) (exteriorPower.map n g.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp]; simp)
      (by rw [← exteriorPower.map_comp]; simp)
  refine IsBaseChange.of_equiv (e₁.trans e₂) fun x => ?_

  have key : ∀ x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))),
      (e₁.trans e₂) ((1 : A) ⊗ₜ[R] x) = F x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [LinearEquiv.trans_apply, he₁, one_smul, hF]
      show exteriorPower.map n g.toLinearMap (exteriorPower.ιMulti A n fun i => (1 : A) ⊗ₜ[R] m i) = _
      rw [exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      show hf.equiv ((1 : A) ⊗ₜ[R] m i) = f (m i)
      rw [IsBaseChange.equiv_tmul, one_smul]
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [map_smul, ← hy, TensorProduct.tmul_smul, ← algebraMap_smul A r ((1 : A) ⊗ₜ[R] y), map_smul,
        algebraMap_smul]
  exact key x (by rw [exteriorPower.ιMulti_span]; trivial)
