import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits

set_option autoImplicit false

theorem ValuationSubring.exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (a : AlgebraicClosure ℚ) (ha : a ∈ P) :
    ∃ c : AlgebraicClosure ℚ, c ∈ IntermediateField.fixedField (P.inertiaSubgroupIn F) ∧ c ∈ P ∧
      ∃ h : a - c ∈ P, (⟨a - c, h⟩ : ↥P) ∈ IsLocalRing.maximalIdeal ↥P := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits.solution
