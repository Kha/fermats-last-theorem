import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open Polynomial IsLocalRing

theorem Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
    (q : ℕ) [Fact q.Prime] (hq : 2 ≤ q)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (g : Polynomial (PowerSeries W₀)) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀))
    (hg0 : ∃ u : PowerSeries W₀, IsUnit u ∧ g.coeff 0 = (q : PowerSeries W₀) * u) :
    Prime g ∧ IsDomain (AdjoinRoot g) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul.solution
