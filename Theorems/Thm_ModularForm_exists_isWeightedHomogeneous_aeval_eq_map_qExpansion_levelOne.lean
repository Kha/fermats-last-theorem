import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

open scoped MatrixGroups

theorem ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ),
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom (ZMod ℓ)),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom (ZMod ℓ))] : Fin 2 → PowerSeries (ZMod ℓ)) Φ =
          T.map (Int.castRingHom (ZMod ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne.solution
