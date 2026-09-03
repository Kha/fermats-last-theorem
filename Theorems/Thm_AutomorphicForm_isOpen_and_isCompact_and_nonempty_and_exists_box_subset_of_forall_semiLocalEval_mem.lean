import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

open scoped Classical

theorem AutomorphicForm.isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S₁ : Finset (HeightOneSpectrum (𝓞 K)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 K), Set (Fin 2 → L ⊗[K] v.adicCompletion K))
    (hUo : ∀ v ∈ S₁, IsOpen (Uloc v)) (hUc : ∀ v ∈ S₁, IsCompact (Uloc v))
    (hU0 : ∀ v ∈ S₁, (0 : Fin 2 → L ⊗[K] v.adicCompletion K) ∈ Uloc v)
    (hUstd : ∀ v ∉ S₁, Uloc v = {x | ∀ i, x i ∈ AutomorphicForm.semiLocalIntegers K L v})
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (hU : U = {a | ∀ v : HeightOneSpectrum (𝓞 K), (fun i => AutomorphicForm.semiLocalEval K L v (a i)) ∈ Uloc v}) :
    IsOpen U ∧ IsCompact U ∧ U.Nonempty ∧
      ∃ n : ℕ, 0 < n ∧ ∀ x : Fin 2 → FiniteAdeleRing (𝓞 L) L,
        (∀ i, x i ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) →
          (fun i => ((n : ℕ) : FiniteAdeleRing (𝓞 L) L) * x i) ∈ U := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOpen_and_isCompact_and_nonempty_and_exists_box_subset_of_forall_semiLocalEval_mem.solution
