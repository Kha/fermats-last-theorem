import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap
    (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (Λ : JHNeronObjectAtP.LevelData p M H hpM A) :
    ∃ ρ : baseRing p →+* ↥A, A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ) ∧ Λ.σA = Spec.map (CommRingCat.ofHom ρ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_ringHom_comp_eq_algebraMap_and_sigmaA_eq_specMap.solution
