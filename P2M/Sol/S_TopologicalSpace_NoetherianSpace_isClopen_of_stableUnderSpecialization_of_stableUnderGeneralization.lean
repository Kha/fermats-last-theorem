import Mathlib
import P2M.Util
namespace P2MW.S_TopologicalSpace_NoetherianSpace_isClopen_of_stableUnderSpecialization_of_stableUnderGeneralization

set_option autoImplicit false

universe u

namespace T1TopoLC

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem isClosed_of_stable {s : Set X}
    (h₁ : StableUnderSpecialization s) (h₂ : StableUnderGeneralization s) : IsClosed s := by

  have key : ∀ C ∈ irreducibleComponents X, (C ∩ s).Nonempty → C ⊆ s := by
    intro C hC hCs z hz
    obtain ⟨y, hyC, hys⟩ := hCs
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    have hξs : ξ ∈ s := h₂ (hξ.specializes hyC) hys
    exact h₁ (hξ.specializes hz) hξs
  have hs : s = ⋃ C ∈ {C ∈ irreducibleComponents X | (C ∩ s).Nonempty}, C := by
    apply le_antisymm
    · intro x hx
      refine Set.mem_biUnion (x := irreducibleComponent x) ⟨irreducibleComponent_mem_irreducibleComponents x,
        ⟨x, mem_irreducibleComponent, hx⟩⟩ mem_irreducibleComponent
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      exact key C hC.1 hC.2 hxC
  rw [hs]
  exact (NoetherianSpace.finite_irreducibleComponents.subset (fun C hC => hC.1)).isClosed_biUnion
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

end T1TopoLC

theorem solution
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {s : Set X}
    (h₁ : StableUnderSpecialization s) (h₂ : StableUnderGeneralization s) : IsClopen s := by
  exact ⟨T1TopoLC.isClosed_of_stable h₁ h₂,
    by
      have := T1TopoLC.isClosed_of_stable (s := sᶜ) h₂.compl h₁.compl
      rwa [isClosed_compl_iff] at this⟩
