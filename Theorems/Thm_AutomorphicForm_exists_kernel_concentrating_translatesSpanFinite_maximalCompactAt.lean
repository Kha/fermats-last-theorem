import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
    (K : Type) [Field K] [NumberField K] :
    ∃ κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ,
      (∀ n, Continuous (κ n)) ∧ (∀ n k, 0 ≤ κ n k) ∧ (∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1) ∧
      (∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
        Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0)) ∧
      (∀ n, ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
        (fun k => κ n (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt.solution
