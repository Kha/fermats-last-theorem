import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

theorem MeasureTheory.exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R]
    (α : Measure R) [SFinite α] [α.IsAddLeftInvariant]
    (Λ : AddSubgroup R) [Countable Λ]
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ)
    (hfin : ∀ C : Set R, IsCompact C → (C ∩ (Λ : Set R)).Finite)
    (hdiv : ∀ x ∈ Λ, x ≠ 0 → ∃ u : Rˣ, (u : R) = x ∧ ((u⁻¹ : Rˣ) : R) ∈ Λ)
    (F : Set R) (hF : IsAddFundamentalDomain Λ F α)
    (C₀ : Set R) (hC₀ : IsCompact C₀) (hlt : α F < α C₀) :
    ∃ C : Set Rˣ, IsCompact C ∧
      ∀ t : Rˣ, Measure.map (fun x : R => (t : R) * x) α = α →
        Measure.map (fun x : R => x * (t : R)) α = α →
        ∃ l : Rˣ, (l : R) ∈ Λ ∧ ((l⁻¹ : Rˣ) : R) ∈ Λ ∧ ∃ k ∈ C, t = l * k := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain.solution
