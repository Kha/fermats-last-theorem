import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import P2M.Util
namespace P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup

open FLT.SmoothVectors

theorem solution (p : ℕ) [Fact p.Prime] :
    gl2CongruenceSubgroup p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    have ha := PadicInt.algebraMap_apply (p := p) a
    have hb := PadicInt.algebraMap_apply (p := p) b
    rw [ha, hb] at hab
    exact Subtype.coe_injective hab
  have mem_range_iff : ∀ {x : ℚ_[p]},
      x ∈ Set.range (algebraMap ℤ_[p] ℚ_[p]) ↔ ‖x‖ ≤ 1 := by
    intro x
    rw [FLT.SpectralSide.range_algebraMap_padicInt p]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hradius : ((p : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  ext g
  rw [mem_gl2CongruenceSubgroup_iff,
    FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj g]
  simp only [hradius]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h1 i j)),
           fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h2 i j))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h1 i j)),
           fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h2 i j))⟩
