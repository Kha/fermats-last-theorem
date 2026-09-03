import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_finite_of_isLocallyFlatCocycleAd_zero

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) : Finite k := by
  obtain ⟨H, _, _, hfin, hfl, hcc, e, he_add, he_act⟩ := hflat
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
  haveI : Finite (H →ₐ[ℤ_[p]] PadicAlgCl p) := Finite.algHom ℤ_[p] H (PadicAlgCl p)
  haveI : Finite (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) :=
    Finite.of_equiv _ (WithConv.equiv (H →ₐ[ℤ_[p]] PadicAlgCl p)).symm
  haveI : Finite (ρbar.V × ρbar.V) := Finite.of_equiv _ e
  haveI : Finite ρbar.V :=
    Finite.of_injective (fun v : ρbar.V => (v, (0 : ρbar.V))) fun a b h => (Prod.mk.inj h).1
  haveI : Nontrivial ρbar.V := Module.nontrivial_of_finrank_pos (R := k) (by rw [ρbar.finrank_eq]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : ρbar.V)
  exact Finite.of_injective (fun c : k => c • v) (smul_left_injective k hv)
