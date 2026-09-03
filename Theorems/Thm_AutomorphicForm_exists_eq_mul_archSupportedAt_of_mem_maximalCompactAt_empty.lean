import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
    (F : Type) [Field F] [NumberField F] (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F ∅) (w : InfinitePlace F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F,
      k = k₁ * k₂ ∧ k₁ * k₂ = k₂ * k₁ ∧
      glFin (𝓞 F) F k₁ = 1 ∧
      (∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k₁) = 1) ∧
      archComponent F w (glArch (𝓞 F) F k₁) = archComponent F w (glArch (𝓞 F) F k) ∧
      (∀ w' : InfinitePlace F, IsRowIsometry (archComponent F w' (glArch (𝓞 F) F k₁))) ∧
      k₂ ∈ maximalCompactAt F ∅ ∧ archComponent F w (glArch (𝓞 F) F k₂) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty.solution
