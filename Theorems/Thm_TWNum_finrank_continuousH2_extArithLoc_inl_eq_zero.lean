import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem TWNum.finrank_continuousH2_extArithLoc_inl_eq_zero
    {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    finrank k
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_TWNum_finrank_continuousH2_extArithLoc_inl_eq_zero.solution
