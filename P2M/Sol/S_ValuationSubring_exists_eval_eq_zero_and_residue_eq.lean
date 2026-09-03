import Mathlib
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_eval_eq_zero_and_residue_eq

open Polynomial

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (q : Polynomial A) (hq : IsUnit q.leadingCoeff)
    (a₀ : IsLocalRing.ResidueField A)
    (hroot : (q.map (IsLocalRing.residue A)).eval a₀ = 0) :
    ∃ α : A, q.eval α = 0 ∧ IsLocalRing.residue A α = a₀ := by
  classical
  set u : (↥A)ˣ := hq.unit with hu
  set qm : Polynomial ↥A := C ((↑u⁻¹ : ↥A)) * q with hqm
  have hqmq : q = C (↑u : ↥A) * qm := by
    rw [hqm, ← mul_assoc, ← C_mul]
    have : ((u : ↥A) * (↑u⁻¹ : ↥A)) = 1 := by
      simp
    rw [this, C_1, one_mul]
  have hqu : q.leadingCoeff = u := (IsUnit.unit_spec hq).symm
  have hlc : qm.Monic := by
    show qm.leadingCoeff = 1
    rw [hqm, leadingCoeff_mul, leadingCoeff_C, hqu]
    simp
  have hspl : (qm.map (algebraMap ↥A L)).Splits := IsAlgClosed.splits _
  have hinj : Function.Injective (algebraMap ↥A L) := Subtype.val_injective
  have hrange : ∀ a ∈ (qm.map (algebraMap ↥A L)).roots, a ∈ (algebraMap ↥A L).range := by
    intro a ha
    have hne : qm.map (algebraMap ↥A L) ≠ 0 := (hlc.map _).ne_zero
    have hev : (qm.map (algebraMap ↥A L)).eval a = 0 := (mem_roots hne).mp ha
    have hint : IsIntegral ↥A a :=
      ⟨qm, hlc, by rwa [eval_map] at hev⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
    exact ⟨y, hy⟩
  have hsA : qm.Splits := Splits.of_splits_map_of_injective hinj hspl hrange
  have hfac : qm = (qm.roots.map fun a => X - C a).prod := hsA.eq_prod_roots_of_monic hlc
  have hres_qm : (qm.map (IsLocalRing.residue ↥A)).eval a₀ = 0 := by
    have : qm.map (IsLocalRing.residue ↥A)
        = C (IsLocalRing.residue ↥A (↑u⁻¹ : ↥A)) * q.map (IsLocalRing.residue ↥A) := by
      rw [hqm, Polynomial.map_mul, Polynomial.map_C]
    rw [this, eval_mul, hroot, mul_zero]
  have hprod : ((qm.roots.map fun a => a₀ - IsLocalRing.residue ↥A a)).prod = 0 := by
    have h1 : (qm.map (IsLocalRing.residue ↥A)).eval a₀ = 0 := hres_qm
    rw [hfac, Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map] at h1
    convert h1 using 3
    · rfl
    simp [Polynomial.map_sub, eval_sub]
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ qm.roots, a₀ - IsLocalRing.residue ↥A a = 0 := by
    have h0 : (0 : IsLocalRing.ResidueField ↥A)
        ∈ (qm.roots.map fun a => a₀ - IsLocalRing.residue ↥A a) :=
      Multiset.prod_eq_zero_iff.mp hprod
    obtain ⟨a, ha, hzero⟩ := Multiset.mem_map.mp h0
    exact ⟨a, ha, hzero⟩
  refine ⟨a, ?_, ?_⟩
  · have hne : qm ≠ 0 := hlc.ne_zero
    have hroota : qm.eval a = 0 := (mem_roots hne).mp ha
    rw [hqmq, eval_mul, hroota, mul_zero]
  · exact (sub_eq_zero.mp hza).symm
