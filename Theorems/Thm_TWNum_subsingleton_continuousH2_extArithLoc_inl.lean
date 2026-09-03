import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_TWNum_subsingleton_continuousH2_extArithLoc_inl
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem TWNum.subsingleton_continuousH2_extArithLoc_inl
    {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    Subsingleton
      (continuousH2 (extArithLoc S (Sum.inl ())) (Rep.res (extArithLoc S (Sum.inl ())) M)) := by p2m_exact_reverting @_root_.P2MW.S_TWNum_subsingleton_continuousH2_extArithLoc_inl.solution
