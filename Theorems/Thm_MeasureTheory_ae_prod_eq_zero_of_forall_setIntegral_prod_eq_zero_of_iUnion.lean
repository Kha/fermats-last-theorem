import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (k : X × X → ℂ)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
    (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n)
    (hint : ∀ n, IntegrableOn k (S n ×ˢ S n) (μ.prod μ))
    (hzero : ∀ n, ∀ A ⊆ S n, MeasurableSet A → ∀ B ⊆ S n, MeasurableSet B →
      ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
    k =ᵐ[μ.prod μ] 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion.solution
