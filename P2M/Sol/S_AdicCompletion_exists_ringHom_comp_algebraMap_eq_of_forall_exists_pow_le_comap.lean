import Mathlib
import P2M.Util
namespace P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "Valued AdicCompletion P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap.AdicCompletion"

namespace AdicCompletion
p2m_export "AdicCompletion" "evalₐ liftRingHom of AdicCauchySequence ext evalₐ_of algebraMap_apply induction_on AdicCauchySequence.mk_eq_mk evalₐ_mk"
namespace ValuedLift
p2m_open "AdicCompletion"

variable {B : Type*} [CommRing B] (𝔪 : Ideal B)
variable {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S]
variable (ev : B →+* S)

theorem exists_monotone_modulus (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ N : ℕ → ℕ, Monotone N ∧ ∀ k, 𝔪 ^ N k ≤ (J ^ k).comap ev := by
  choose n hn using hcont
  refine ⟨fun k => (Finset.range (k + 1)).sup n, fun a b hab => Finset.sup_mono (Finset.range_mono (by omega)), fun k => ?_⟩
  exact (Ideal.pow_le_pow_right (Finset.le_sup (f := n) (Finset.self_mem_range_succ k))).trans (hn k)

end AdicCompletion.ValuedLift

open Valued _root_.AdicCompletion _root_.P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap.AdicCompletion AdicCompletion.ValuedLift in

theorem solution
    {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ ψ : AdicCompletion 𝔪 B →+* S, ψ.comp (algebraMap B (AdicCompletion 𝔪 B)) = ev := by
  obtain ⟨N, hNmono, hN⟩ := exists_monotone_modulus 𝔪 J ev hcont

  let f : (k : ℕ) → AdicCompletion 𝔪 B →+* S ⧸ J ^ k := fun k =>
    (Ideal.quotientMap (J ^ k) ev (hN k)).comp (evalₐ 𝔪 (N k)).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    apply RingHom.ext
    intro x
    induction x using AdicCompletion.induction_on with
    | _ a =>
      simp only [f, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalₐ_mk,
        Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

      rw [Ideal.Quotient.eq, ← map_sub]
      apply hN m
      have h := AdicCauchySequence.mk_eq_mk (hNmono hle) a
      rw [Submodule.Quotient.eq] at h
      simpa [smul_eq_mul, Ideal.mul_top] using h
  refine ⟨IsAdicComplete.liftRingHom J f hf, ?_⟩
  apply RingHom.ext
  intro b
  rw [RingHom.comp_apply]

  apply eq_of_sub_eq_zero
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := J) (R := S))
  intro k
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
  simp only [f, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of, Ideal.quotientMap_mk]
