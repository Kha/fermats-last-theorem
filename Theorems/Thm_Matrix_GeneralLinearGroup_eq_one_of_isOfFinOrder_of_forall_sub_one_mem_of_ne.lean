import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne

set_option autoImplicit false

open scoped MatrixGroups
theorem Matrix.GeneralLinearGroup.eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne
    (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    (𝔪₁ 𝔪₂ : Ideal A) (h𝔪₁ : 𝔪₁.IsMaximal) (h𝔪₂ : 𝔪₂.IsMaximal)
    (p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) (hp₁𝔪 : (p₁ : A) ∈ 𝔪₁) (hp₂𝔪 : (p₂ : A) ∈ 𝔪₂)
    (n : Type) [Fintype n] [DecidableEq n]
    (g : Matrix.GeneralLinearGroup n A) (hg : IsOfFinOrder g)
    (hg₁ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₁)
    (hg₂ : ∀ i j : n, (g : Matrix n n A) i j - (1 : Matrix n n A) i j ∈ 𝔪₂) :
    g = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_eq_one_of_isOfFinOrder_of_forall_sub_one_mem_of_ne.solution
