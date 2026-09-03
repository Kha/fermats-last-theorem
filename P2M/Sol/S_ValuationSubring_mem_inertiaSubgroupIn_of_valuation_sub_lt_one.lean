import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
namespace P2MW.S_ValuationSubring_mem_inertiaSubgroupIn_of_valuation_sub_lt_one

open scoped Pointwise

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hσA : σ • A = A)
    (h : ∀ a ∈ A, A.valuation (σ a - a) < 1) :
    σ ∈ A.inertiaSubgroupIn K := by
  let d : A.decompositionSubgroup K := ⟨σ, hσA⟩
  refine ⟨d, ?_, rfl⟩
  change (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)) d = 1
  ext x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  change d • IsLocalRing.residue A a = IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  exact h a a.2
