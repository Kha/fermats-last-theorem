import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

theorem MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.solution
