import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_pullbackAlong_liesOver_of_liesOver

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pullbackAlong_liesOver_of_liesOver
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [AlgebraicCurve.IsCurveOver E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    [AlgebraicCurve.HasPrincipalDivisors K F'] [AlgebraicCurve.HasPrincipalDivisors E F'E]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (D : AlgebraicCurve.Divisor K F) (DE : AlgebraicCurve.Divisor E FE)
    (hover : ∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
      v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring → DE v' = D v)
    (hoff : ∀ v' : AlgebraicCurve.Place E FE,
      (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) → DE v' = 0) :
    (∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
        w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring →
        AlgebraicCurve.Divisor.pullbackAlong φE hφE DE w' = AlgebraicCurve.Divisor.pullbackAlong φ hφ D w) ∧
    (∀ w' : AlgebraicCurve.Place E F'E,
        (∀ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) ≠ w.toValuationSubring) →
        AlgebraicCurve.Divisor.pullbackAlong φE hφE DE w' = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_liesOver_of_liesOver.solution
