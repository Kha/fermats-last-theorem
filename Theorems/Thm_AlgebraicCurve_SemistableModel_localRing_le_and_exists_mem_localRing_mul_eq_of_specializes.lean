import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes

set_option autoImplicit false

open AlgebraicCurve AlgebraicGeometry CategoryTheory

theorem AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
    {F : Type} [Field F] (X : Scheme.{0}) [IsIntegral X] (φ : F ≃+* X.functionField)
    {x η : X} (h : η ⤳ x) :
    SemistableModel.localRing X φ x ≤ SemistableModel.localRing X φ η ∧
    ∀ z : F, z ∈ SemistableModel.localRing X φ η →
      ∃ f g : F, f ∈ SemistableModel.localRing X φ x ∧ g ∈ SemistableModel.localRing X φ x ∧
        (∃ g' ∈ SemistableModel.localRing X φ η, g * g' = 1) ∧ z * g = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes.solution
