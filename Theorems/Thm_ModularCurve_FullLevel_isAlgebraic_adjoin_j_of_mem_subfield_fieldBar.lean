import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_isAlgebraic_adjoin_j_of_mem_subfield_fieldBar

set_option autoImplicit false

p2m_open "ModularCurve~finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange ModularCurve.FullLevel"

theorem ModularCurve.FullLevel.isAlgebraic_adjoin_j_of_mem_subfield_fieldBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (A₀ : Type) [CommRing A₀]
    (F₀ : Subfield ↥(fieldBar q M'))
    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
    [Algebra A₀ ↥F₀] :
    ∀ x : ↥F₀, IsAlgebraic ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_isAlgebraic_adjoin_j_of_mem_subfield_fieldBar.solution
