import Mathlib
import P2M.Util
import P2M.Sol.S_exists_residueField_of_isMaximal_of_finiteDimensional

universe u v

theorem exists_residueField_of_isMaximal_of_finiteDimensional
    (F : Type u) [Field F] [CharZero F]
    (A : Type v) [CommRing A] [Algebra F A] [FiniteDimensional F A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : Algebra.IsSeparable F K)
      (θ : A →ₐ[F] K), Function.Surjective θ ∧ ∀ a : A, θ a = 0 ↔ a ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_exists_residueField_of_isMaximal_of_finiteDimensional.solution
