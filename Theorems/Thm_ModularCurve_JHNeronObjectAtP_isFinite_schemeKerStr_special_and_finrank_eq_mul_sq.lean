import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
attribute [-simp] ModularCurve.JZeroNeronAtPData.mk.sizeOf_spec ModularCurve.JZeroNeronAtPData.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (hB : IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)) :
    IsFinite ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ O.toricRank *
         Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.solution
