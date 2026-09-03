import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete

set_option autoImplicit false

universe u

open IsLocalRing Polynomial

theorem IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    (LinearMap.mulLeft W a).charpoly.Monic ∧
    (LinearMap.mulLeft W a).charpoly.natDegree = Module.finrank W O ∧
    (∀ i : ℕ, i ≤ Module.finrank W O →
      ((Module.finrank W O - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) ≤
        (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W a).charpoly.coeff i)) ∧
    ((Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) =
      (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W a).charpoly.coeff 0)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete.solution
