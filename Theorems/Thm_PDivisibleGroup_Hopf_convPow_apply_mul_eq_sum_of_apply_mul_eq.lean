import Mathlib
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq

set_option autoImplicit false

universe u v w

theorem PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq
    {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Bialgebra R A]
    {Λ : Type w} [CommSemiring Λ] [Algebra R Λ] (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = Coalgebra.counit (R := R) a • d b + Coalgebra.counit (R := R) b • d a)
    (k : ℕ) (a b : A) :
    (WithConv.toConv d ^ k).ofConv (a * b) =
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : Λ) *
        ((WithConv.toConv d ^ j).ofConv a * (WithConv.toConv d ^ (k - j)).ofConv b) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq.solution
