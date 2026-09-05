import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Sol.S_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import P2M.Util
namespace P2MW.S_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] :
    ∃ h : LaurentSeries ℤ, qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * h := by
  classical
  set D : LaurentSeries ℤ := qExpand ℤ q jqInt - jqInt ^ q with hD

  have hj : laurentMap (Int.castRingHom (ZMod q)) jqInt = jqModC (ZMod q) := by
    rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
    rfl
  have hred : laurentMap (Int.castRingHom (ZMod q)) D = 0 := by
    rw [hD, map_sub, map_pow, laurentMap_qExpand, hj, ModularCurve.qExpand_jqModC_eq_pow_unconditional, sub_self]

  have hdvd : ∀ k : ℤ, (q : ℤ) ∣ D.coeff k := fun k => by
    have h0 : (laurentMap (Int.castRingHom (ZMod q)) D).coeff k = 0 := by rw [hred]; rfl
    rw [laurentMap_coeff] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  choose c hc using hdvd
  have hsupp : (Function.support c).IsPWO := by
    refine D.isPWO_support.mono ?_
    intro k hk
    rw [Function.mem_support] at hk
    rw [HahnSeries.mem_support, hc k]
    exact mul_ne_zero (by exact_mod_cast (Fact.out : q.Prime).ne_zero) hk
  refine ⟨⟨c, hsupp⟩, ?_⟩
  ext k
  rw [hc k, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℤ)) q, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
