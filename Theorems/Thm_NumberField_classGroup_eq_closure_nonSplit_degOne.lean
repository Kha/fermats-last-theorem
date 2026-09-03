import Definitions.Def_NumberField_IsSplitPrime
import P2M.Util
import P2M.Sol.S_NumberField_classGroup_eq_closure_nonSplit_degOne
set_option autoImplicit false
namespace NumberField
open scoped NumberField nonZeroDivisors
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]
theorem classGroup_eq_closure_nonSplit_degOne (q : ℕ) (hq : q.Prime)
    (h3q : 3 ≤ q) (hdeg : Module.finrank K M = q) :
    (⊤ : Subgroup (ClassGroup (𝓞 K))) =
      Subgroup.closure {c | ∃ (P : (Ideal (𝓞 K))⁰),
        (P : Ideal (𝓞 K)).IsMaximal ∧ (Ideal.absNorm (P : Ideal (𝓞 K))).Prime ∧
        ¬ IsSplitPrime K M P ∧ c = ClassGroup.mk0 P} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_classGroup_eq_closure_nonSplit_degOne.solution
