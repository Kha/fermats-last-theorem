import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit
set_option autoImplicit false

theorem IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit
    {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
    (ϖ : O) (hϖ : Irreducible ϖ)
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (g h w : R) (hw : IsUnit w) (e : ℕ) (he : 1 ≤ e)
    (hgh : g * h = algebraMap O R ϖ ^ e * w)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap O R ϖ, g, h})
    (hg : (Ideal.span {algebraMap O R ϖ, g}).IsPrime) (hh : (Ideal.span {algebraMap O R ϖ, h}).IsPrime)
    (hhg : h ∉ Ideal.span {algebraMap O R ϖ, g}) (hgh' : g ∉ Ideal.span {algebraMap O R ϖ, h})
    (h2 : IsUnit (2 : R)) :
    IsIntegrallyClosed R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit.solution
