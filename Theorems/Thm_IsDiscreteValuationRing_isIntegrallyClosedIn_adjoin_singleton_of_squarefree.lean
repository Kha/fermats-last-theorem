import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree

theorem IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F ϖ ^ n * x ∈ Algebra.adjoin O {α}) :
    IsIntegrallyClosedIn (Algebra.adjoin O {α}) F := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree.solution
