import Mathlib
import P2M.Util
namespace P2MW.S_LinearMap_exists_injective_range_eq_ker_of_isTorsion

universe u v

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {D : Type v} [AddCommGroup D] [Module A D] (hD : Module.IsTorsion A D)
    {r : ℕ} (π : (Fin r → A) →ₗ[A] D) :
    ∃ φ : (Fin r → A) →ₗ[A] (Fin r → A),
      Function.Injective φ ∧ LinearMap.range φ = LinearMap.ker π := by
  classical
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun A (Fin r)) (LinearMap.ker π)
  have hf : Function.Surjective snf.f := by
    intro j
    by_contra hj
    have hj' : j ∉ Set.range snf.f := hj
    obtain ⟨⟨c, hc0⟩, hc⟩ := @hD (π (snf.bM j))
    have hmem : c • snf.bM j ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_smul]
      exact hc
    have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hj'
    simp at h0
    exact nonZeroDivisors.ne_zero hc0 h0
  have hn : n = r := le_antisymm
    (by simpa using Fintype.card_le_of_embedding snf.f)
    (by simpa using Fintype.card_le_of_surjective snf.f hf)
  let b : Module.Basis (Fin r) A (LinearMap.ker π) := snf.bN.reindex (finCongr hn)
  refine ⟨(LinearMap.ker π).subtype ∘ₗ (b.equivFun.symm : (Fin r → A) →ₗ[A] LinearMap.ker π),
    ?_, ?_⟩
  · exact Subtype.val_injective.comp b.equivFun.symm.injective
  · rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr b.equivFun.symm.surjective,
      Submodule.map_top, Submodule.range_subtype]
