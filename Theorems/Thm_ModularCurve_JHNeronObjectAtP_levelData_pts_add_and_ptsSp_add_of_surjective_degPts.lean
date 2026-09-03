import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_levelData_pts_add_and_ptsSp_add_of_surjective_degPts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.levelData_pts_add_and_ptsSp_add_of_surjective_degPts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (hsurj : Function.Surjective (O.degPts 0))

    (degPull0 : SchemeHomOver Λ.f O.g)
    (hpull_mul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) degPull0 = O.L.mul s (schemeHomOverComp x degPull0) (schemeHomOverComp y degPull0))

    (Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hpullsp0 : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x degPull0)) = (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))) :
    (∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) ∧
    (∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_levelData_pts_add_and_ptsSp_add_of_surjective_degPts.solution
