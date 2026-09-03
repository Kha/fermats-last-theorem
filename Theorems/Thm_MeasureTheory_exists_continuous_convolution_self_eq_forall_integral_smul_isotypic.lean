import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ e : K → ℂ, Continuous e ∧ (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : K →* (H →L[ℂ] H)), (∀ (k : K) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : K => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic.solution
