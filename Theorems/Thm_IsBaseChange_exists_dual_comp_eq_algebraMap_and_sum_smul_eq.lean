import Mathlib
import P2M.Util
import P2M.Sol.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq

set_option autoImplicit false

universe u v w w'

open scoped BigOperators

theorem IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
    {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']
    {M : Type w} [AddCommGroup M] [Module A M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    (f : M →ₗ[A] M') (hf : IsBaseChange A' f)
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
    ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m' := by p2m_exact_reverting @_root_.P2MW.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq.solution
