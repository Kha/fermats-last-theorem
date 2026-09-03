import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
    {k : ℤ} (f : ModularForm 𝒮ℒ k) (T : PowerSeries ℚ)
    (hT : T.map (algebraMap ℚ ℂ) = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) ℚ,
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom ℚ),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom ℚ)] : Fin 2 → PowerSeries ℚ) Φ = T := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne.solution
