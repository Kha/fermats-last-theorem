import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Order
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mem_span_C_sup_ofList_take_iff

open MvPowerSeries
theorem MvPowerSeries.mem_span_C_sup_ofList_take_iff {R : Type*} [CommRing R] (ϖ : R) (n k : ℕ) (F : MvPowerSeries (Fin n) R) :
    F ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) R)} ⊔
        Ideal.ofList ((List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take k) ↔
      ∀ m : Fin n →₀ ℕ, (∀ j : Fin n, (j : ℕ) < k → m j = 0) → ϖ ∣ coeff m F := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mem_span_C_sup_ofList_take_iff.solution
