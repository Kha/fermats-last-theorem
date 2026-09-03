import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import P2M.Util
namespace P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one

set_option autoImplicit false

theorem solution
    {K : Type} [CommRing K] (p : ℕ) (c ζ : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (ModularCurve.slotSubst K p (ζ * c) j ModularCurve.tateUnivX) -
        PowerSeries.coeff n (ModularCurve.slotSubst K p c j ModularCurve.tateUnivX) ∈
      Ideal.span {((ζ : K) - 1)} := by
  rw [← Ideal.Quotient.eq]
  set π := Ideal.Quotient.mk (Ideal.span {((ζ : K) - 1)}) with hπ
  have hζ : π (ζ : K) = 1 := by
    rw [← map_one π, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hζi : π ((ζ⁻¹ : Kˣ) : K) = 1 := by
    have h : π ((ζ⁻¹ : Kˣ) : K) * π (ζ : K) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rwa [hζ, mul_one] at h
  rw [ModularCurve.coeff_slotSubst_tateUnivX p (ζ * c) j hj hjp n,
    ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp n]
  simp only [map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, apply_ite π, map_zero,
    Units.val_mul, mul_inv, mul_pow, hζ, hζi, one_pow, one_mul]

#print axioms solution
