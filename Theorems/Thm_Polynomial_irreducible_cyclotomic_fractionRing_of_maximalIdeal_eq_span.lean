import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span

set_option autoImplicit false

theorem Polynomial.irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : ℕ) [Fact q.Prime]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) :
    Irreducible (Polynomial.cyclotomic q (FractionRing A₀)) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span.solution
