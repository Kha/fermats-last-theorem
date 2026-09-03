import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
namespace P2MW.S_CuspForm_heckeLocal_residue_pi

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

open scoped TensorProduct
open CuspForm

noncomputable section

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) [Fact (CuspForm.HasIntegralStructure N 2)] (t : ↥(CuspForm.heckeAlgebra N 2 S)) : IsLocalRing.residue (CuspForm.heckeLocal N S 𝒪 θ) (CuspForm.heckeLocal.π N S 𝒪 θ t) = IsLocalRing.ResidueField.map (algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) (θ t) := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (θ t)
  have hx : (1 : 𝒪) ⊗ₜ[ℤ] t - algebraMap 𝒪 _ a ∈ heckeCharKernel N S 𝒪 θ := by
    rw [mem_heckeCharKernel_iff, map_sub, residualCharacter_tmul, residualCharacter_algebraMap,
      map_one, one_mul, ha, sub_self]
  have h1 : algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)
      (latticeBaseChange N S 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] t) - algebraMap 𝒪 _ a) ∈
        IsLocalRing.maximalIdeal (heckeLocal N S 𝒪 θ) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (heckeLocal N S 𝒪 θ) (heckeLocalIdeal N S 𝒪 θ),
      ← latticeBaseChange_algebraMap, ← map_sub]
    exact Ideal.mem_map_of_mem _ hx
  rw [map_sub, ← IsScalarTower.algebraMap_apply, ← Ideal.Quotient.eq] at h1
  rw [← ha, IsLocalRing.ResidueField.map_residue]
  exact h1

end
