import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.NumberTheory.Cyclotomic.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModularCurve.PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (conj : Fin (p + 1) → LaurentSeries (CyclotomicField p ℚ))
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p
      (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p))⁻¹))
    (c : ℕ → LaurentSeries ℚ)
    (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k =
      ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.qExpand ℚ p (c k)))
    (k : ℕ) : c k ∈ Algebra.adjoin ℚ {ModularCurve.jq} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.solution
