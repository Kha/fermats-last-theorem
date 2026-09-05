import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (p : ℕ) (hp : p ≠ 0) (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦi : Φ.toRingHom.IsIntegral) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p)
    (w : AlgebraicCurve.Place K L) :
    w.restrictAlong Φ hΦi = g • w := by

  have hpow : ∀ (A : ValuationSubring L) (y : L), y ^ p ∈ A ↔ y ∈ A := by
    intro A y
    refine ⟨fun h => ?_, fun h => A.pow_mem h p⟩
    rw [← A.valuation_le_one_iff] at h ⊢
    rw [map_pow] at h
    exact (pow_le_one_iff_of_nonneg zero_le' hp).mp h
  ext1
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show Φ x ∈ w.toValuationSubring ↔ _
  rw [hΦ x, hpow]

