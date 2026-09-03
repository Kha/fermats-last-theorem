import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
namespace P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero

set_option autoImplicit false

namespace IharaLemmaSolCorner

open IharaLemma

theorem smul_eq_zero_of_notMem {B : Type} [CommRing B] (S : IdempotentSplitting B) {M : Type}
    [AddCommGroup M] [Module B M] {u : B} {y : M} (huy : u • y = 0) {j : Fin S.n} (hu : u ∉ S.𝔪 j) :
    S.e j • y = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.coi.idem j) (S.𝔪 j)
    (fun J hJ hne => S.mem_of_isMaximal_of_ne j J hJ hne) hu
  rw [← ht, mul_right_comm, mul_smul, huy, smul_zero]

end IharaLemmaSolCorner

theorem solution {B : Type} [CommRing B]
    (S : IharaLemma.IdempotentSplitting B) {M : Type} [AddCommGroup M] [Module B M]
    {u : B} {y : M} (huy : u • y = 0) (i₀ : Fin S.n) (hu : ∀ j, j ≠ i₀ → u ∉ S.𝔪 j) :
    y = S.e i₀ • y := by
  have hsum : (∑ j, S.e j) • y = y := by rw [S.coi.complete, one_smul]
  conv_lhs => rw [← hsum, Finset.sum_smul]
  rw [Finset.sum_eq_single i₀ (fun j _ hj => IharaLemmaSolCorner.smul_eq_zero_of_notMem S huy (hu j hj))
    (fun h => absurd (Finset.mem_univ i₀) h)]
