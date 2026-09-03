import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP
  GoodReductionJacobian NeronModelInfra IsLocalRing
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) (hpm : m.Coprime p)
    (x : JH M H) (hx : x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m) :
    x ∈ O.toricPts m ↔
      ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        ∀ i : Fin 2, fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) =
          Λ.L.one (resPt A ≫ Λ.σA) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one.solution
