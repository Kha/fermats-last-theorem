import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm
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
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hcommφ : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hcommψ : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))

    (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hFIE : AlgebraicCurve.FundamentalIdentityAlong E φE hφE) (hfinE : AlgebraicCurve.FiniteAlong E ψE)
    (hNE : AlgebraicCurve.NormFormulaAlong E ψE hfinE)

    (ι : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 E FE)
    (hpin : ∀ (D : AlgebraicCurve.Divisor.degZero (K := K) (F := F)) (D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE)),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) →
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0) →
      ι (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D')
    (hex : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F), ∃ D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) ∧
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0)) :
    ∀ x : AlgebraicCurve.Pic0 K F,
      ι (AlgebraicCurve.Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
        AlgebraicCurve.Pic0.correspondence φE ψE hφE hψE hFIE hfinE hNE (ι x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm.solution
