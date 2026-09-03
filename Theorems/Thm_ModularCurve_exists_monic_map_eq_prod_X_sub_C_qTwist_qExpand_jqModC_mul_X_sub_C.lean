import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open Polynomial open ModularCurve hiding nonempty_modularPolynomialData

universe u

theorem ModularCurve.exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (e : ℕ) [NeZero e] (heℓ : ¬ ℓ ∣ e)
    (F : IntermediateField κ (LaurentSeries κ))
    (hmem : ModularCurve.qExpand κ (ℓ * e) (ModularCurve.jqModC κ) ∈ F) :
    ∃ P : Polynomial ↥F, P.Monic ∧ P.natDegree = ℓ + 1 ∧
      P.map (algebraMap ↥F (LaurentSeries κ)) =
        (∏ k ∈ Finset.range ℓ,
            (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) (ModularCurve.qExpand κ e (ModularCurve.jqModC κ))))) *
          (Polynomial.X - Polynomial.C (ModularCurve.qExpand κ (ℓ * (ℓ * e)) (ModularCurve.jqModC κ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C.solution
