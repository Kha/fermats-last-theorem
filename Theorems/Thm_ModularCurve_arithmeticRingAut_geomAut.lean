import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_arithmeticRingAut_geomAut

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticRingAut_geomAut (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) : arithmeticRingAut F₀ τ (geomAut L F₀ σ x) = geomAut L F₀ σ (arithmeticRingAut F₀ τ x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_arithmeticRingAut_geomAut.solution
