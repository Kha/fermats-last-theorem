import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_schemeHomOverComp_torusFibre_degeneracyHom_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.schemeHomOverComp_torusFibre_degeneracyHom_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre) (O.degeneracyHom i) =
      Λ.L.one (torusStr (ResidueField ↥A) O.toricRank ≫ resPt A ≫ Λ.σA) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_schemeHomOverComp_torusFibre_degeneracyHom_eq_one.solution
