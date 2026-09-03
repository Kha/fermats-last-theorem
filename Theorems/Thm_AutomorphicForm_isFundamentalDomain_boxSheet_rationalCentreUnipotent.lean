import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isFundamentalDomain_boxSheet_rationalCentreUnipotent
    (K : Type) [Field K] [NumberField K] :
    let P : Subgroup (AdelicGL2 (𝓞 K) K) :=
      rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range
    let T : Set (rationalCentreUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    P ≤ rationalCentreUnipotent K ∧ Countable P ∧ MeasurableSet T ∧
    IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent K)) T (rationalCentreUnipotentHaar K) ∧
    ∀ F : rationalCentreUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalCentreUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent.solution
