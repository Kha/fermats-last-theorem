import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
namespace P2MW.S_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two

theorem solution (N : ℕ) : CuspForm.HasIntegralBasis N ↔ CuspForm.HasIntegralStructure N 2 := by
  have hset : CuspForm.qIntegralSet N =
      {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2 | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} := by
    ext f
    simp only [CuspForm.qIntegralSet, Set.mem_setOf_eq]
    refine forall_congr' fun n => ?_
    rw [Subring.mem_bot]
    exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩
  unfold CuspForm.HasIntegralBasis CuspForm.HasIntegralStructure CuspForm.intLattice
  rw [hset, Submodule.span_span_of_tower]
