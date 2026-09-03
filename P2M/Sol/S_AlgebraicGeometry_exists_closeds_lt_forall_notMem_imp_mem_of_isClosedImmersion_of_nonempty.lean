import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : Closeds X) (hT : Set.range i.base = (T : Set X))
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' := by
  have hce : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  refine ⟨⟨i.base '' ((U : Set Z)ᶜ), hce.isClosedMap _ U.isOpen.isClosed_compl⟩, ?_, fun z hz => ⟨z, hz, rfl⟩⟩
  rw [SetLike.lt_iff_le_and_exists]
  obtain ⟨u, hu⟩ := hU
  refine ⟨?_, i.base u, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := (Closeds.mem_mk).mp hx
    have : i.base z ∈ (T : Set X) := hT ▸ ⟨z, rfl⟩
    exact this
  · have : i.base u ∈ (T : Set X) := hT ▸ ⟨u, rfl⟩
    exact this
  · intro h
    obtain ⟨z, hz, hzu⟩ := (Closeds.mem_mk).mp h
    exact hz (by rwa [hce.injective hzu])
