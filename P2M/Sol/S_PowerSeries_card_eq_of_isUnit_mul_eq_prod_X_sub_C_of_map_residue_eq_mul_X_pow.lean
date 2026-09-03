import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
namespace P2MW.S_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] {ι : Type*} (S : Finset ι) (z : ι → T)
    (hz : ∀ i ∈ S, z i ∈ maximalIdeal T) (f u : PowerSeries T) (hu : IsUnit u) (N : ℕ)
    (hf : ∃ v : PowerSeries (ResidueField T), IsUnit v ∧ PowerSeries.map (residue T) f = v * PowerSeries.X ^ N)
    (h : u * f = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) :
    S.card = N := by
  classical
  obtain ⟨v, hv, hfv⟩ := hf

  have hred := congrArg (PowerSeries.map (residue T)) h
  rw [map_mul, hfv, map_prod] at hred
  have hfac : ∀ i ∈ S, PowerSeries.map (residue T) (PowerSeries.X - PowerSeries.C (z i)) = PowerSeries.X := by
    intro i hi
    rw [map_sub, PowerSeries.map_X, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr (hz i hi), map_zero, sub_zero]
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, ← mul_assoc] at hred

  set w : PowerSeries (ResidueField T) := PowerSeries.map (residue T) u * v with hw
  have hwu : IsUnit w := (hu.map _).mul hv
  have hw0 : PowerSeries.constantCoeff w ≠ 0 := by
    intro h0
    have := PowerSeries.isUnit_iff_constantCoeff.mp hwu
    rw [h0] at this
    exact not_isUnit_zero this
  have hc := congrArg (PowerSeries.coeff N) hred
  rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_X_pow] at hc
  by_contra hne
  rw [if_neg (fun h => hne h.symm)] at hc
  exact hw0 hc
