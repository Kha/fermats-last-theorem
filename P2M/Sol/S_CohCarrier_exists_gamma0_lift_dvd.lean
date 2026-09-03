import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Inst
import P2M.Util
namespace P2MW.S_CohCarrier_exists_gamma0_lift_dvd

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, gamma0Units M σ = d ∧ ((ℓ * M : ℕ) : ℤ) ∣ ((σ : SL(2, ℤ)) 1 0) := by
  have hdvd : M ∣ ℓ * M := dvd_mul_left M ℓ
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd d
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective (ℓ * M) u
  have hτ0 : ((τ : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 (ℓ * M) := τ.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ0
  have hσ0 : ((τ : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hτ0
  refine ⟨⟨(τ : SL(2, ℤ)), hσ0⟩, ?_, hτ0⟩
  apply Units.ext
  rw [val_gamma0Units, ← hu, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hτ, val_gamma0Units]
  show (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ZMod.castHom hdvd (ZMod M) ((((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (ℓ * M)))
  rw [map_intCast]
