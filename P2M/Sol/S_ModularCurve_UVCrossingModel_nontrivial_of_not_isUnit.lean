import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] {π : W} (hπ : ¬IsUnit π) :
    Nontrivial (UVCrossingModel W π) :=
  by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop => hπ ?_
  have h1 : (1 : MvPowerSeries (Fin 2) W) ∈ uvCrossingIdeal W π := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.mp h1
  have hcc := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)) hf
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C, zero_mul, zero_sub, mul_neg] at hcc
  refine IsUnit.of_mul_eq_one (-(MvPowerSeries.constantCoeff f)) ?_
  rw [mul_comm, neg_mul]
  exact hcc
