import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_zero_of_mem_toricPts_pow
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (n : ℕ) (hn : 0 < n) (x : JH M H) (hx : x ∈ O.toricPts (p ^ n))
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1)
    (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (hsκ : sκ.1 = resPt A ≫ s.1) :
    O.ptsSp.symm sκ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow.solution
