import Mathlib
import Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
import Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
import P2M.Util
namespace P2MW.S_Algebra_Etale_finite_and_bijective_lift_pi_algHom_algebraicClosure

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace EvalBij

variable (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A]

noncomputable def pointsEquiv (Ω : Type u) [Field Ω] [Algebra K Ω] :
    ((Ω ⊗[K] A) →ₐ[Ω] Ω) ≃ (A →ₐ[K] Ω) where
  toFun χ := (χ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  invFun ν := Algebra.TensorProduct.lift (Algebra.ofId Ω Ω) ν (fun _ _ => Commute.all _ _)
  left_inv χ := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext a
      simp [Algebra.TensorProduct.includeRight_apply]
  right_inv ν := by
    ext a
    simp

noncomputable abbrev evalMap :
    AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
      (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
    (Pi.algHom K _
      fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
    (fun _ _ => Commute.all _ _)

theorem evalMap_apply_eq (x : AlgebraicClosure K ⊗[K] A) (ν : A →ₐ[K] AlgebraicClosure K) :
    evalMap K A x (WithConv.toConv ν) = (pointsEquiv K A (AlgebraicClosure K)).symm ν x := by

  have h : (Pi.evalAlgHom (AlgebraicClosure K) (fun _ => AlgebraicClosure K) (WithConv.toConv ν)).comp (evalMap K A)
      = (pointsEquiv K A (AlgebraicClosure K)).symm ν := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext a
      simp [evalMap, pointsEquiv]
  exact congrArg (fun f => f x) (congrArg DFunLike.coe h)

theorem main [Module.Finite K A] [Algebra.Etale K A] :
    Finite (WithConv (A →ₐ[K] AlgebraicClosure K)) ∧ Function.Bijective (evalMap K A) := by
  classical
  set Ω := AlgebraicClosure K

  haveI : Algebra.Etale Ω (Ω ⊗[K] A) := inferInstance
  haveI : Module.Finite Ω (Ω ⊗[K] A) := inferInstance

  have hcard : Nat.card (A →ₐ[K] Ω) = Module.finrank K A := by
    rw [← Nat.card_congr (pointsEquiv K A Ω), Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed Ω (Ω ⊗[K] A),
      Module.finrank_baseChange]
  have hcardW : Nat.card (WithConv (A →ₐ[K] Ω)) = Module.finrank K A := by
    rw [Nat.card_congr (WithConv.equiv (A →ₐ[K] Ω)), hcard]

  have hfin : Finite (WithConv (A →ₐ[K] Ω)) := by
    by_cases h0 : Module.finrank K A = 0
    ·
      haveI : Subsingleton A := Module.finrank_zero_iff.mp h0
      haveI : IsEmpty (WithConv (A →ₐ[K] Ω)) := ⟨fun ν => zero_ne_one (α := Ω) (by
        have h1 := map_one (WithConv.ofConv ν)
        rw [Subsingleton.elim (1 : A) 0, map_zero] at h1
        exact h1)⟩
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcardW ▸ h0)
  refine ⟨hfin, ?_⟩
  haveI := hfin
  haveI : Fintype (WithConv (A →ₐ[K] Ω)) := Fintype.ofFinite _

  have hinj : Function.Injective (evalMap K A) := by
    intro x y hxy
    apply Algebra.Etale.eq_of_forall_algHom_apply_eq (K := Ω) (Ω := Ω)
    intro χ
    have hx := evalMap_apply_eq K A x (pointsEquiv K A Ω χ)
    have hy := evalMap_apply_eq K A y (pointsEquiv K A Ω χ)
    rw [Equiv.symm_apply_apply] at hx hy
    rw [← hx, ← hy, hxy]

  have hdim : Module.finrank Ω (Ω ⊗[K] A) = Module.finrank Ω (WithConv (A →ₐ[K] Ω) → Ω) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, ← hcardW, Nat.card_eq_fintype_card]
  refine ⟨hinj, ?_⟩
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (show Function.Injective (evalMap K A).toLinearMap from hinj)
  exact this

end EvalBij

theorem solution
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] :
    Finite (WithConv (A →ₐ[K] AlgebraicClosure K)) ∧
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) :=
  EvalBij.main K A
