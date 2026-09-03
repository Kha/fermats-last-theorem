import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL

set_option autoImplicit false

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (c : Kˣ) (d : (Omega K π).obj B) :
    (Omega.action K π).act B (scalarGL c) d = d := by
  have hinv : (scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ = scalarGL c⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])
  apply DeligneDatum.ext'
  funext M
  show (d.line (FullLattice.act (scalarGL c)⁻¹ M)).comap (actBaseChange B (scalarGL c)⁻¹ M).toLinearMap = d.line M
  rw [hinv, d.homothety c⁻¹ M]
  exact Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL c⁻¹) M).injective _
