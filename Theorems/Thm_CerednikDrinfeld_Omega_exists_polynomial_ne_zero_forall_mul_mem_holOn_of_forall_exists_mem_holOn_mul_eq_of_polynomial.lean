import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ)
    {ι : Type} [Fintype ι] (S : ι → Set K) (hS : ∀ i, S i ⊆ affinoid ϖ n)
    (F : ↥(affinoid ϖ n) → K)
    (P : ι → Polynomial K) (hP : ∀ i, P i ≠ 0)
    (f : (i : ι) → ↥(S i) → K) (hf : ∀ i, f i ∈ holOn K (S i))
    (hrep : ∀ (i : ι) (z : ↥(S i)), (P i).eval (z : K) ≠ 0 → (P i).eval (z : K) * F ⟨(z : K), hS i z.2⟩ = f i z) :
    ∃ g : Polynomial K, g ≠ 0 ∧
      ∀ i : ι, (fun z : ↥(S i) => g.eval (z : K) * F ⟨(z : K), hS i z.2⟩) ∈ holOn K (S i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_polynomial_ne_zero_forall_mul_mem_holOn_of_forall_exists_mem_holOn_mul_eq_of_polynomial.solution
