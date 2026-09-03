import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing

set_option autoImplicit false

theorem Algebra.Etale.exists_sum_mul_smul_eq_ite_of_isLocalRing
    {W W' : Type*} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
    (hcard : Fintype.card Γ = Module.finrank W W') :
    ∃ (n : ℕ) (x y : Fin n → W'), ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing.solution
