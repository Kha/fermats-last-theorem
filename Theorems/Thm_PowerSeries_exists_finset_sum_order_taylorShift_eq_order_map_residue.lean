import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue

theorem PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue
    {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (F : PowerSeries O) (hF : F.map (IsLocalRing.residue O) ≠ 0) :
    ∃ S : Finset L, (∀ r, r ∈ S ↔ ‖r‖ < 1 ∧
        0 < (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order) ∧
      ∑ r ∈ S, (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order
        = (F.map (IsLocalRing.residue O)).order := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue.solution
