import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (r : Fin n → AdelicGL2 (𝓞 K) K),
      (∀ i, r i ∈ adelicMaximalCompact K ∧ r i ∈ finiteAdelicGL2Subgroup K) ∧
      ∀ k ∈ adelicMaximalCompact K, k ∈ finiteAdelicGL2Subgroup K →
        ∃ i, (r i)⁻¹ * k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finset_adelicMaximalCompact_finiteAdelic_coset_principalLevel.solution
