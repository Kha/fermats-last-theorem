import Definitions.Def_ModularCurve_PhiGen
import P2M.Sol.S_ModularCurve_phiIrreducible_of_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
import P2M.Sol.S_ModularCurve_evalAtJGen_injective
import P2M.Util
namespace P2MW.S_ModularCurve_modularPolynomialData_phi_unique_of_prime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve IntermediateField

theorem solution {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ.Prime) (data data' : ModularCurve.ModularPolynomialData ℓ) :
    data.Φ = data'.Φ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h3 : data.Φ.map ModularCurve.evalAtJGen = data'.Φ.map ModularCurve.evalAtJGen :=
    (data.minpoly_jqN_eq (ModularCurve.phiIrreducible_of_prime ℓ data)).symm.trans
      (data'.minpoly_jqN_eq (ModularCurve.phiIrreducible_of_prime ℓ data'))
  exact Polynomial.map_injective ModularCurve.evalAtJGen ModularCurve.evalAtJGen_injective h3
