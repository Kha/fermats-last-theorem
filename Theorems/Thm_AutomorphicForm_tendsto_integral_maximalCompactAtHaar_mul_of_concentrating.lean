import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.tendsto_integral_maximalCompactAtHaar_mul_of_concentrating
    (K : Type) [Field K] [NumberField K]
    (κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ)
    (hκc : ∀ n, Continuous (κ n)) (hκ0 : ∀ n k, 0 ≤ κ n k) (hκ1 : ∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1)
    (hκU : ∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
      Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (x : AdelicGL2 (𝓞 K) K) :
    Filter.Tendsto (fun n => ∫ k, (κ n k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) Filter.atTop
      (nhds (f x)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_tendsto_integral_maximalCompactAtHaar_mul_of_concentrating.solution
