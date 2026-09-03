import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
    (K : Type) [Field K] [NumberField K] :
    ∃ κ R θ : ℝ, 1 ≤ κ ∧ 0 < θ ∧
      ∀ (c u d₁ d₂ : ℝ), ∀ g ∈ centreCutSiegelSet K c u d₁ d₂,
        ∃ δ : GL (Fin 2) K,
          (∃ (ε : (𝓞 K)ˣ) (β : 𝓞 K),
              (δ : Matrix (Fin 2) (Fin 2) K) =
                !![((ε : 𝓞 K) : K), ((β : 𝓞 K) : K); 0, (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)]) ∧
          globalPoints (𝓞 K) K δ * g ∈ centreCutSiegelSetAmple K (θ * c) R d₁ d₂ κ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple.solution
