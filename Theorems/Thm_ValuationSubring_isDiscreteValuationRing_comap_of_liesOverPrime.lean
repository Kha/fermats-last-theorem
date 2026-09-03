import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime

theorem ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    IsDiscreteValuationRing (A.comap (algebraMap L (AlgebraicClosure ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime.solution
