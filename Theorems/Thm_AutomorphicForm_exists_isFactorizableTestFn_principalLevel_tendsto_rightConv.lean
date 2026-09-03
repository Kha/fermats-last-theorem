import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isFactorizableTestFn_principalLevel_tendsto_rightConv

set_option autoImplicit false

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.exists_isFactorizableTestFn_principalLevel_tendsto_rightConv
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 K) K → ℂ),
      (∀ n, IsFactorizableTestFn K (f n)) ∧
      (∀ n (x : AdelicGL2 (𝓞 K) K), f n x ≠ 0 →
        ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧
          k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      (∀ n (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f n (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f n y) ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
          φ (g * k) = φ g) →
        ∀ g : AdelicGL2 (𝓞 K) K,
          Filter.Tendsto (fun n => rightConv K φ (f n) g) Filter.atTop (nhds (φ g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_principalLevel_tendsto_rightConv.solution
