import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
namespace P2MW.S_ModularCurve_JZero_exists_addEquiv_placeEquiv_oneMul

set_option autoImplicit false
open AlgebraicCurve ModularCurve

namespace LTPaux

open AlgebraicCurve ModularCurve

theorem aux (M M' : ℕ) [Fact M.Prime] [Fact M'.Prime] (h : M = M') :
    ∃ (eLT : JZero M ≃+ JZero M')
      (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) ≃
              Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')),
      (∀ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M))))
          (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M')))),
        (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) =
            Finsupp.mapDomain ePl (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) →
        eLT (Pic0.mk D₁) = Pic0.mk D₂) ∧
      (∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M))
          (f : ↥(modularFunctionFieldBar M)) (f' : ↥(modularFunctionFieldBar M')),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
          (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f') ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)),
        ePl (arithmeticGalois (modularFunctionFieldFull M) σ • V) = arithmeticGalois (modularFunctionFieldFull M') σ • ePl V) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero M), eLT (σ • x) = σ • eLT x) ∧
      eisensteinNumerator M = eisensteinNumerator M' := by
  subst h
  refine ⟨AddEquiv.refl _, Equiv.refl _, ?_, ?_, ?_, ?_, rfl⟩
  · intro D₁ D₂ hD
    rw [Equiv.coe_refl, Finsupp.mapDomain_id] at hD
    have : D₂ = D₁ := Subtype.ext hD
    subst this
    rfl
  · intro V f f' hff
    have : f = f' := Subtype.ext hff
    subst this
    exact ⟨Iff.rfl, rfl⟩
  · intro σ V; rfl
  · intro σ x; rfl

end LTPaux

open AlgebraicCurve ModularCurve

theorem solution (p : ℕ) [Fact p.Prime] :
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

      eisensteinNumerator (1 * p) = eisensteinNumerator p := by
  haveI : Fact (1 * p).Prime := ⟨(Nat.one_mul p).symm ▸ Fact.out⟩
  exact LTPaux.aux (1 * p) p (Nat.one_mul p)
