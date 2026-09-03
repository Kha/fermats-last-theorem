import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
namespace P2MW.S_FormalGroup_IsBaseChange_nthSeries_eq_map

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (h : F.IsBaseChange f G) (n : ℕ) :
    G.nthSeries n = PowerSeries.map f (F.nthSeries n) := by
  induction n with
  | zero => simp [FormalGroup.nthSeries_zero]
  | succ n ih =>
    rw [FormalGroup.nthSeries_succ, FormalGroup.nthSeries_succ, ih]
    unfold FormalGroup.IsBaseChange at h
    rw [h]
    have e1 : ∀ p : PowerSeries R, PowerSeries.map f p = MvPowerSeries.map f p := fun p => rfl
    have hv : (fun i => MvPowerSeries.map f
        ((![F.nthSeries n, PowerSeries.X] : Fin 2 → PowerSeries R) i)) =
        ![MvPowerSeries.map f (F.nthSeries n), PowerSeries.X] := by
      funext i
      fin_cases i
      · rfl
      · show MvPowerSeries.map f PowerSeries.X = PowerSeries.X
        exact PowerSeries.map_X f
    simp only [e1]
    rw [MvPowerSeries.map_subst (F.hasSubst_nthSeries n), hv]
