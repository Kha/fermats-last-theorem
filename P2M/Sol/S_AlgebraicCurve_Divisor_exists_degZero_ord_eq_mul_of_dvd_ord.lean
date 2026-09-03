import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
set_option Elab.async false

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    (hdvd : ∀ v : Place K F, (n : ℤ) ∣ v.ord f) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  have h0 : ((0 : ℤ) / (n : ℤ)) = 0 := by simp
  set D0 : Divisor K F := Finsupp.mapRange (· / (n : ℤ)) h0 Df with hD0
  have hsmul : (n : ℤ) • D0 = Df := by
    ext v
    rw [Finsupp.smul_apply, hD0, Finsupp.mapRange_apply, smul_eq_mul]
    refine Int.mul_ediv_cancel' ?_
    rw [hDf v]
    exact hdvd v
  have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hdeg0 : D0 ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero]
    have h1 : (n : ℤ) * Divisor.degree D0 = 0 := by
      rw [← smul_eq_mul, ← map_zsmul, hsmul, hdeg]
    exact (mul_eq_zero.mp h1).resolve_left hnz
  refine ⟨⟨D0, hdeg0⟩, fun v => ?_⟩
  show v.ord f = (n : ℤ) * D0 v
  rw [← hDf v, ← hsmul, Finsupp.smul_apply, smul_eq_mul]

#print axioms solution
