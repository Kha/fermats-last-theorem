import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly

universe u

theorem IsIntegrallyClosed.isReduced_quotient_span_singleton_of_squarefree_minpoly
    {R A O F : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F]
    [Algebra R A] [Algebra R O] [Algebra R F] [Algebra A F] [Algebra O F]
    [IsScalarTower R A F] [IsScalarTower R O F]
    [FaithfulSMul R A] [FaithfulSMul A F] [FaithfulSMul O F] [Algebra.IsIntegral R A]
    {p : R} (hp : (Ideal.span {p}).IsPrime) (hp0 : p ≠ 0)
    (hpO : Irreducible (algebraMap R O p))
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {p}, ∃ r : R, algebraMap R O r = algebraMap R O s * x)
    {α : F} (hα : IsIntegral O α)
    (hαA : ∃ s ∉ Ideal.span {p}, ∃ a : A, algebraMap A F a = algebraMap R F s * α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {algebraMap R O p}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F (algebraMap R O p) ^ n * x ∈ Algebra.adjoin O {α}) :
    IsReduced (A ⧸ Ideal.span {algebraMap R A p}) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly.solution
