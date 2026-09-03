import Mathlib
import P2M.Util
namespace P2MW.S_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

universe u

open TensorProduct

set_option autoImplicit false

theorem solution
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1 := by
  have hq : Module.rankAtStalk (R := K) (K ⊗[R] P) ⟨⊥, Ideal.isPrime_bot⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange]; exact h _
  rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hq
  haveI : Nontrivial (Localization.AtPrime (⊥ : Ideal K)) := by infer_instance
  rwa [Module.finrank_baseChange] at hq
