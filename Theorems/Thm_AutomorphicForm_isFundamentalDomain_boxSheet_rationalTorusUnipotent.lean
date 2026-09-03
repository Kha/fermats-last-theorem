import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent
    (K : Type) [Field K] [NumberField K] :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.solution
