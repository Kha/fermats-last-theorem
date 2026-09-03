import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_exists_addEquiv_placeEquiv_oneMul

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_addEquiv_placeEquiv_oneMul (p : ℕ) [Fact p.Prime] :
    haveI : Fact (1 * p).Prime := ⟨(Nat.one_mul p).symm ▸ Fact.out⟩
    ∃ (eLT : JZero (1 * p) ≃+ JZero p)
      (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃
              Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)),

      (∀ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
          (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)))),
        (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
            Finsupp.mapDomain ePl (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        eLT (Pic0.mk D₁) = Pic0.mk D₂) ∧

      (∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
          (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
          (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f') ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
        ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (1 * p)), eLT (σ • x) = σ • eLT x) ∧

      eisensteinNumerator (1 * p) = eisensteinNumerator p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_exists_addEquiv_placeEquiv_oneMul.solution
