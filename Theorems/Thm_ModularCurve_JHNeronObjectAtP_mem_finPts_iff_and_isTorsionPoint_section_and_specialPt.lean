import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    (∀ x : JH M H, x ∈ O.finPts m ↔
      x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x)) ∧
    (∀ s : SchemeHomOver Λ.σA O.g, O.L.IsTorsionPoint Λ.σA m s →
      O.pts.symm (schemeHomOverComp (barPt A) Λ.hσA s) ∈ O.finPts m) ∧
    (∀ x ∈ O.finPts m, ∀ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 → O.L.IsTorsionPoint Λ.σA m s) ∧
    (∀ s : SchemeHomOver Λ.σA O.g, O.L.IsTorsionPoint Λ.σA m s →
      ∀ sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g, sκ.1 = resPt A ≫ s.1 → O.L.IsTorsionPoint (resPt A ≫ Λ.σA) m sκ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt.solution
