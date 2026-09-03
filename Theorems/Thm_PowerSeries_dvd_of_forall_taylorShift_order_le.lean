import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_dvd_of_forall_taylorShift_order_le

theorem PowerSeries.dvd_of_forall_taylorShift_order_le
    {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (P Q : PowerSeries O) (hQ : Q.map (IsLocalRing.residue O) ≠ 0)
    (h : ∀ r : L, ‖r‖ < 1 →
      (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (Q.map ι) * ((n + k).choose n : L) * r ^ k).order
        ≤ (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (P.map ι) * ((n + k).choose n : L) * r ^ k).order) :
    Q ∣ P := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.solution
