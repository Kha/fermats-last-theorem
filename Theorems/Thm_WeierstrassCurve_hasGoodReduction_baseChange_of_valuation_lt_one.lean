import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_hasGoodReduction_baseChange_of_valuation_lt_one

theorem WeierstrassCurve.hasGoodReduction_baseChange_of_valuation_lt_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) [E.HasGoodReduction R]
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (S : ValuationSubring L) [IsDiscreteValuationRing S]
    {q : ℕ} (hq : q.Prime) (hqR : Irreducible (q : R)) (hS : S.valuation (q : L) < 1) :
    (E.baseChange L).HasGoodReduction S := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasGoodReduction_baseChange_of_valuation_lt_one.solution
