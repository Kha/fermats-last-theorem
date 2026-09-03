import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaLemma_exists_isCompl_orthogonal_of_isIdempotentElem_of_selfAdjoint

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.exists_isCompl_orthogonal_of_isIdempotentElem_of_selfAdjoint
    {𝒪 : Type} [CommRing 𝒪] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module B' V'] [IsScalarTower 𝒪 B' V']
    (U : Submodule B' V') (Bf : ↥(U.restrictScalars 𝒪) →ₗ[𝒪] ↥(U.restrictScalars 𝒪) →ₗ[𝒪] 𝒪)
    (hadj : ∀ (t : B') (x y : ↥(U.restrictScalars 𝒪)),
      Bf ⟨t • (x : V'), U.smul_mem t x.2⟩ y = Bf x ⟨t • (y : V'), U.smul_mem t y.2⟩)
    (e : B') (he : IsIdempotentElem e) :
    ∃ C : Submodule B' V', C ≤ U ∧
      (∀ u ∈ U, ∃ u₁ u₂ : V', u₁ ∈ U ∧ e • u₁ = u₁ ∧ u₂ ∈ C ∧ u = u₁ + u₂) ∧
      (∀ v : V', v ∈ U → e • v = v → v ∈ C → v = 0) ∧
      (∀ (x y : ↥(U.restrictScalars 𝒪)), e • (x : V') = x → (y : V') ∈ C → Bf x y = 0 ∧ Bf y x = 0) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_exists_isCompl_orthogonal_of_isIdempotentElem_of_selfAdjoint.solution
