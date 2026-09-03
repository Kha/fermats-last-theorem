import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated

theorem PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u.map (IsLocalRing.residue A) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun p : PowerSeries ℤ => p.map (Int.castRingHom (IsLocalRing.ResidueField A))) ''
            (N : Set (PowerSeries ℤ))) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated.solution
