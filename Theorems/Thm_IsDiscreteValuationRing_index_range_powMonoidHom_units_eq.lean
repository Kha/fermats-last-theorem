import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem IsDiscreteValuationRing.index_range_powMonoidHom_units_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)] {n : ℕ} (hn : (n : R) ≠ 0) :
    (powMonoidHom n : Rˣ →* Rˣ).range.index
      = Nat.card (rootsOfUnity n R) * Nat.card (R ⧸ Ideal.span {(n : R)}) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq.solution
