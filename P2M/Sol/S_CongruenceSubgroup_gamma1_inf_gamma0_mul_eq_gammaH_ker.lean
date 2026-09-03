import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
namespace P2MW.S_CongruenceSubgroup_gamma1_inf_gamma0_mul_eq_gammaH_ker

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) =
      CohCarrier.GammaH (N * ℓ) (ZMod.unitsMap (dvd_mul_right N ℓ)).ker := by
  ext A
  rw [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, CongruenceSubgroup.Gamma1_mem]
  constructor
  · rintro ⟨⟨_, h11, _⟩, hA0⟩
    refine ⟨hA0, ?_⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units,
      Units.val_one]
    show ZMod.cast (((A 1 1 : ℤ) : ZMod (N * ℓ))) = (1 : ZMod N)
    rw [ZMod.cast_intCast (dvd_mul_right N ℓ)]
    exact h11
  · rintro ⟨hA0, hker⟩
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units,
      Units.val_one] at hker
    change ZMod.cast (((A 1 1 : ℤ) : ZMod (N * ℓ))) = (1 : ZMod N) at hker
    rw [ZMod.cast_intCast (dvd_mul_right N ℓ)] at hker
    have h10 : ((A 1 0 : ℤ) : ZMod N) = 0 := by
      have h := CongruenceSubgroup.Gamma0_mem.mp hA0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
      exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N ℓ)).trans h
    refine ⟨⟨?_, hker, h10⟩, hA0⟩
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have h := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hker, h10, mul_one, mul_zero,
      sub_zero] at h
    exact h
