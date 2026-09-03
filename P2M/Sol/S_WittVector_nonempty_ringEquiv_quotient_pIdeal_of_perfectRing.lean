import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
namespace P2MW.S_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Nonempty (k ≃+* (WittVector p k ⧸ pIdeal p (WittVector p k))) := by
  classical
  let π : WittVector p k →+* k := WittVector.constantCoeff
  have hπ : ∀ x : WittVector p k, π x = x.coeff 0 := fun x => WittVector.constantCoeff_apply x
  have hsurj : Function.Surjective π := fun a =>
    ⟨WittVector.teichmuller p a, by rw [hπ, WittVector.teichmuller_coeff_zero]⟩
  have hker : RingHom.ker π = pIdeal p (WittVector p k) := by
    ext x
    rw [RingHom.mem_ker, hπ]
    constructor
    · intro hx0
      have hV : WittVector.verschiebung (x.shift 1) = x := by
        have h := WittVector.verschiebung_shift x 0 (fun i hi => by
          interval_cases i
          exact hx0)
        have h0 : x.shift 0 = x := by ext n; simp [WittVector.shift_coeff]
        rw [h0] at h
        exact h
      set z := (WittVector.frobeniusEquiv p k).symm (x.shift 1) with hzdef
      have hz : WittVector.frobenius z = x.shift 1 := (WittVector.frobeniusEquiv p k).apply_symm_apply _
      rw [← hV, ← hz, WittVector.verschiebung_frobenius]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · intro hx
      have hle : pIdeal p (WittVector p k) ≤ RingHom.ker π := by
        rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
        exact CharP.cast_eq_zero k p
      have := hle hx
      rwa [RingHom.mem_ker, hπ] at this
  exact ⟨(RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker)⟩
