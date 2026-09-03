import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_arithmeticRingAut_geomAut
import P2M.Util
namespace P2MW.S_ModularCurve_arithmeticGalois_smul_geomAut

open ModularCurve AlgebraicCurve
open scoped TensorProduct

theorem solution (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) :
    arithmeticGalois F₀ τ • geomAut L F₀ σ x = geomAut L F₀ σ (arithmeticGalois F₀ τ • x) := by
  rw [SemilinearAut.smul_def, SemilinearAut.smul_def, toRingAut_arithmeticGalois]
  exact ModularCurve.arithmeticRingAut_geomAut L F₀ τ σ x
