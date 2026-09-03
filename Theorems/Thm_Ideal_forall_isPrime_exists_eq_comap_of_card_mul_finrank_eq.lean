import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq

set_option autoImplicit false

theorem Ideal.forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (𝔭₀ : Ideal R) (h𝔭₀ : 𝔭₀.IsPrime)
    (I : Type) [Fintype I] (e : I → (R ≃ₐ[F] R))
    (hinj : ∀ i i' : I, Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ = Ideal.comap ((e i' : R →ₐ[F] R) : R →+* R) 𝔭₀ → i = i')
    (hcount : Fintype.card I * Module.finrank F (R ⧸ 𝔭₀) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ i : I, 𝔭 = Ideal.comap ((e i : R →ₐ[F] R) : R →+* R) 𝔭₀ := by p2m_exact_reverting @_root_.P2MW.S_Ideal_forall_isPrime_exists_eq_comap_of_card_mul_finrank_eq.solution
