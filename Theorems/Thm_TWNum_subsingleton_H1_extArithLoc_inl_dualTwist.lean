import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist
attribute [-instance] AlgebraicClosure.Rat.isGalois
set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem TWNum.subsingleton_H1_extArithLoc_inl_dualTwist
    {k : Type} [Field k] (S : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional k M]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (hinf : Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) M))) :
    Subsingleton (H1 (Rep.res (extArithLoc S (Sum.inl ())) (M.dualTwist χ))) := by p2m_exact_reverting @_root_.P2MW.S_TWNum_subsingleton_H1_extArithLoc_inl_dualTwist.solution
