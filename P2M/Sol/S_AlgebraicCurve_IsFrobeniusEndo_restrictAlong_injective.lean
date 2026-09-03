import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import P2M.Util
namespace P2MW.S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective

open AlgebraicCurve

private theorem _root_.ValuationSubring.pow_mem_iff' {F : Type*} [Field F]
    (A : ValuationSubring F) {n : ℕ} (hn : n ≠ 0) (x : F) :
    x ^ n ∈ A ↔ x ∈ A := by
  refine ⟨fun hxn => ?_, fun hx => pow_mem hx n⟩
  rcases A.mem_or_inv_mem x with hx | hxi
  · exact hx
  · rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem A
    · have hkey : x = x ^ n * (x⁻¹) ^ (n - 1) := by
        rw [inv_pow, eq_comm, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hx0), ← pow_succ']
        congr 1; omega
      rw [hkey]; exact mul_mem hxn (pow_mem hxi _)

p2m_alias "P2MW.S_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.ValuationSubring.pow_mem_iff'" "ValuationSubring.pow_mem_iff'"
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    {φ : F →ₐ[K] F} {ℓ : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0)
    (hφ : φ.IsIntegral) :
    Function.Injective (AlgebraicCurve.Place.restrictAlong φ hφ) := by
  intro w₁ w₂ hw
  refine AlgebraicCurve.Place.ext (SetLike.ext fun x => ?_)
  obtain ⟨y, hy⟩ := h.pow_mem_range x
  have key : ∀ w : AlgebraicCurve.Place K F,
      x ∈ w.toValuationSubring ↔ y ∈ (w.restrictAlong φ hφ).toValuationSubring := by
    intro w
    letI := AlgebraicCurve.algebraAlong φ
    haveI := AlgebraicCurve.isScalarTower_along φ
    haveI := AlgebraicCurve.isIntegral_along φ hφ
    rw [show AlgebraicCurve.Place.restrictAlong φ hφ w = w.restrict F from rfl,
      AlgebraicCurve.Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
    show x ∈ w.toValuationSubring ↔ φ y ∈ w.toValuationSubring
    rw [hy]
    exact (w.toValuationSubring.pow_mem_iff' hℓ x).symm
  rw [key w₁, key w₂, hw]
