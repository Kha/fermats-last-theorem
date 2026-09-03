import Mathlib
import Theorems.Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one
import P2M.Util
namespace P2MW.S_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

universe u v w

open TensorProduct

theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hπ : Function.Surjective (algebraMap R S)) (hker : IsNilpotent (RingHom.ker (algebraMap R S)))
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (h : Module.Invertible S (S ⊗[R] P)) : Module.Invertible R P := by

  obtain ⟨N, hN⟩ := hker
  have hnil : ∀ a ∈ RingHom.ker (algebraMap R S), IsNilpotent a := fun a ha =>
    ⟨N, by have := Ideal.pow_mem_pow ha N; rw [hN] at this; exact this⟩
  refine Module.Invertible.of_projective_of_forall_finrank_eq_one P fun K _ _ => ?_

  have hkill : ∀ a ∈ RingHom.ker (algebraMap R S), algebraMap R K a = 0 := fun a ha =>
    ((hnil a ha).map (algebraMap R K)).eq_zero
  let e : (R ⧸ RingHom.ker (algebraMap R S)) ≃+* S := RingHom.quotientKerEquivOfSurjective hπ
  let g : S →+* K :=
    (Ideal.Quotient.lift (RingHom.ker (algebraMap R S)) (algebraMap R K) hkill).comp e.symm.toRingHom
  have hg : ∀ r : R, g (algebraMap R S r) = algebraMap R K r := fun r => by
    show Ideal.Quotient.lift _ _ hkill (e.symm (algebraMap R S r)) = _
    have : e.symm (algebraMap R S r) = Ideal.Quotient.mk _ r := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk]
  letI : Algebra S K := g.toAlgebra
  haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r => (hg r).symm

  let ε : K ⊗[S] (S ⊗[R] P) ≃ₗ[K] K ⊗[R] P := TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K P
  haveI : Module.Invertible K (K ⊗[S] (S ⊗[R] P)) := inferInstance
  rw [← ε.finrank_eq]
  exact Module.Invertible.finrank_eq_one (R := K) (M := K ⊗[S] (S ⊗[R] P))
