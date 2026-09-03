import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional
    (K : Type) [Field K] [NumberField K]
    (V : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)) [FiniteDimensional ℂ V]
    (hcont : ∀ φ ∈ V, Continuous φ)
    (hdef : ∀ φ ∈ V,
      (∫ k, φ (k : AutomorphicForm.AdelicGL2 (𝓞 K) K) * conj (φ (k : AutomorphicForm.AdelicGL2 (𝓞 K) K))
        ∂(AutomorphicForm.maximalCompactHaar K)) = 0 → φ = 0) :
    ∃ (n : ℕ) (b : Fin n → (AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)),
      (∀ i, b i ∈ V) ∧
      (∀ i j, ∫ k, b i (k : AutomorphicForm.AdelicGL2 (𝓞 K) K) * conj (b j (k : AutomorphicForm.AdelicGL2 (𝓞 K) K))
          ∂(AutomorphicForm.maximalCompactHaar K) = if i = j then 1 else 0) ∧
      (∀ φ ∈ V, φ ∈ Submodule.span ℂ (Set.range b)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_orthonormal_maximalCompactHaar_basis_of_finiteDimensional.solution
