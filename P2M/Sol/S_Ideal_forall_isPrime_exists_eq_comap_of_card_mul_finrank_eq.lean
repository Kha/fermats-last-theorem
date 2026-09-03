import Mathlib
import Theorems.Thm_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
import P2M.Util
namespace P2MW.S_Ideal_forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq

set_option autoImplicit false

theorem solution
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (𝔭₀ : Ideal R) (h𝔭₀ : 𝔭₀.IsPrime)
    (I : Type) [Fintype I] (e : I → (R ≃ₐ[F] R))
    (hinj : ∀ i i' : I, Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ = Ideal.comap ((e i' : R →ₐ[F] R) : R →+* R) 𝔭₀ → i = i')
    (hcount : Fintype.card I * Module.finrank F (R ⧸ 𝔭₀) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ i : I, 𝔭 = Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ := by
  classical
  let f : I → Ideal R := fun i => Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀
  have hf : ∀ i, f i = Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ := fun i => rfl
  have hf_inj : Function.Injective f := fun i i' h => hinj i i' h
  let S : Finset (Ideal R) := Finset.univ.image f
  have hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime := by
    intro 𝔭 h𝔭
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h𝔭
    haveI := h𝔭₀
    exact Ideal.IsPrime.comap _
  have hrank : ∀ i, Module.finrank F (R ⧸ f i) = Module.finrank F (R ⧸ 𝔭₀) := by
    intro i
    have hmap : 𝔭₀ = (f i).map ((e i : R →ₐ[F] R) : R →+* R) :=
      (Ideal.map_comap_of_surjective ((e i : R →ₐ[F] R) : R →+* R) (e i).surjective 𝔭₀).symm
    exact (Ideal.quotientEquivAlg (f i) 𝔭₀ (e i) hmap).toLinearEquiv.finrank_eq
  have hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R := by
    rw [Finset.sum_image (fun i _ i' _ h => hf_inj h), Finset.sum_congr rfl (fun i _ => hrank i),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, hcount]
  intro 𝔭 h𝔭
  have hmem := Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank F R S hS hsum 𝔭 h𝔭
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi.symm⟩
