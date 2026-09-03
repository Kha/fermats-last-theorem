import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
attribute [-instance] GoodReductionJacobian.RelativeGroupLaw.kerPairStr_isSeparated GoodReductionJacobian.RelativeGroupLaw.kerPairι_isClosedImmersion GoodReductionJacobian.RelativeGroupLaw.kerPairStr_locallyOfFiniteType GoodReductionJacobian.RelativeGroupLaw.kerPairStr_quasiCompact
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.kerPairPointEquiv_mul GoodReductionJacobian.RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe GoodReductionJacobian.RelativeGroupLaw.kerPairPointEquiv_apply_coe_coe GoodReductionJacobian.RelativeGroupLaw.kerPairPointEquiv_one GoodReductionJacobian.RelativeGroupLaw.kerPairPointEquiv_inv GoodReductionJacobian.RelativeGroupLaw.kerPairLift_ι

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (hB : IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)) :
    IsFinite ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ O.toricRank *
         Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.solution
