import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
namespace P2MW.S_CuspForm_heckeLocal_residue_surjective

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

open scoped TensorProduct
open CuspForm

noncomputable section

theorem solution (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪) [Fact (CuspForm.HasIntegralStructure N 2)] : Function.Surjective (IsLocalRing.residue (CuspForm.heckeLocal N S 𝒪 θ) ∘ algebraMap 𝒪 (CuspForm.heckeLocal N S 𝒪 θ)) := by
  intro y
  obtain ⟨q, rfl⟩ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (heckeLocalIdeal N S 𝒪 θ)
      (heckeLocal N S 𝒪 θ)).surjective y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, rfl⟩ := latticeBaseChange_surjective N S 𝒪 b
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (residualCharacter N S 𝒪 θ x)
  refine ⟨a, ?_⟩
  have hx : x - algebraMap 𝒪 _ a ∈ heckeCharKernel N S 𝒪 θ := by
    rw [mem_heckeCharKernel_iff, map_sub, residualCharacter_algebraMap, ha, sub_self]
  have hq : Ideal.Quotient.mk (heckeLocalIdeal N S 𝒪 θ) (latticeBaseChange N S 𝒪 x) =
      Ideal.Quotient.mk _ (algebraMap 𝒪 (heckeBaseAlgebra N S 𝒪) a) := by
    rw [Ideal.Quotient.eq, ← latticeBaseChange_algebraMap, ← map_sub]
    exact Ideal.mem_map_of_mem _ hx
  rw [hq, IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← IsScalarTower.algebraMap_apply]
  rfl

end
