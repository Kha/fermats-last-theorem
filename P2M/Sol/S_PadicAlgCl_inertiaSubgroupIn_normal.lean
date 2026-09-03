import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
namespace P2MW.S_PadicAlgCl_inertiaSubgroupIn_normal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped Pointwise

theorem solution (p : ℕ) [Fact p.Prime] :
    ((padicIntegers p).inertiaSubgroupIn ℚ_[p] : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).Normal := by

  have htop : ValuationSubring.decompositionSubgroup ℚ_[p] (padicIntegers p) = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    rw [MulAction.mem_stabilizer_iff]
    apply SetLike.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, mem_padicIntegers_iff, mem_padicIntegers_iff,
      nnnorm_padicAlgCl_algEquiv]

  haveI : (ValuationSubring.inertiaSubgroup ℚ_[p] (padicIntegers p)).Normal := MonoidHom.normal_ker _
  have hsurj : Function.Surjective (ValuationSubring.decompositionSubgroup ℚ_[p] (padicIntegers p)).subtype := by
    intro σ
    exact ⟨⟨σ, htop ▸ Subgroup.mem_top σ⟩, rfl⟩
  exact Subgroup.Normal.map inferInstance _ hsurj
