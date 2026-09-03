import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.le_of_liesOver_of_forall_smul_eq_of_isInvariant
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (𝔭₀ 𝔭₁ : Ideal B) [𝔭₀.IsPrime] [𝔭₁.IsPrime]
    (h₀ : ∀ g : G, g • 𝔭₀ = 𝔭₀) (h₁ : ∀ g : G, g • 𝔭₁ = 𝔭₁)
    (y : Ideal A) [y.IsPrime] (hy₀ : 𝔭₀.under A ≤ y) (hy₁ : 𝔭₁.under A ≤ y)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.under A = y) :
    𝔭₀ ≤ Q ∧ 𝔭₁ ≤ Q := by p2m_exact_reverting @_root_.P2MW.S_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant.solution
