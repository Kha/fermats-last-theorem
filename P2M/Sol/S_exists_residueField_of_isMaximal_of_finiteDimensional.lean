import Mathlib
import P2M.Util
namespace P2MW.S_exists_residueField_of_isMaximal_of_finiteDimensional

universe u v

theorem solution
    (F : Type u) [Field F] [CharZero F]
    (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : Algebra.IsSeparable F K)
      (θ : A →ₐ[F] K), Function.Surjective θ ∧ ∀ a : A, θ a = 0 ↔ a ∈ 𝔪 := by
  haveI := h𝔪
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : FiniteDimensional F (A ⧸ 𝔪) := inferInstance
  haveI : Algebra.IsSeparable F (A ⧸ 𝔪) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨A ⧸ 𝔪, inferInstance, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ F 𝔪,
    Ideal.Quotient.mkₐ_surjective F 𝔪, fun a => Ideal.Quotient.eq_zero_iff_mem⟩
