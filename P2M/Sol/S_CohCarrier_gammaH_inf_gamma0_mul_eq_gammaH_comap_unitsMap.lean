import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
namespace P2MW.S_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) =
      CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by
  ext A
  rw [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨⟨hA0, hH⟩, hA0'⟩
    refine ⟨hA0', ?_⟩
    rw [Subgroup.mem_comap]
    convert hH using 1
    rw [Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ))) = ((A 1 1 : ℤ) : ZMod M)
    rw [ZMod.cast_intCast (dvd_mul_right M ℓ)]
  · rintro ⟨hA0', hH⟩
    have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by
      have h := CongruenceSubgroup.Gamma0_mem.mp hA0'
      rw [CongruenceSubgroup.Gamma0_mem]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
      exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right M ℓ)).trans h
    refine ⟨⟨hA0, ?_⟩, hA0'⟩
    rw [Subgroup.mem_comap] at hH
    convert hH using 1
    rw [Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ)))
    rw [ZMod.cast_intCast (dvd_mul_right M ℓ)]
