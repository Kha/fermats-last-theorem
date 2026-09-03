import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    ∃ (dom : AddSubgroup (JH M H))
      (sp : ↥dom →+ GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),

      (∀ x : JH M H, x ∈ dom ↔ ExtendsToPlace A Λ.σA (O.pts x)) ∧

      (∀ (x : ↥dom) (s : SchemeHomOver Λ.σA O.g), (O.pts (x : JH M H)).1 = barPt A ≫ s.1 →
        sp x = O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧

      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ dom, σ • x ∈ dom) ∧

      (∀ x ∈ dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • x = 0) → ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) ∧

      (∀ x : ↥dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • (x : JH M H) = 0) → sp x = 0 → x = 0) ∧

      (∀ ξ : GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • ξ = 0) →
          ∃ x : ↥dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • (x : JH M H) = 0) ∧ sp x = ξ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm.solution
