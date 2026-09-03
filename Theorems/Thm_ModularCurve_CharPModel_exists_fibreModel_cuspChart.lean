import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CharPReduction
import Mathlib.FieldTheory.Relrank
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

noncomputable section

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction
theorem ModularCurve.CharPModel.exists_fibreModel_cuspChart
    (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    (hdegX : ∀ i : ℕ, (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i))
    (hliftFin : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y)
    (hliftInf : ∀ y : LaurentSeries k, y ∈ modularFunctionFieldC k N →
      (∃ P : Polynomial (Polynomial k), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)⁻¹)
          y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring red,
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring red f = y) :
    ∃ fm : FibreModel N A ℓ k red, fm.CuspChart := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_exists_fibreModel_cuspChart.solution
