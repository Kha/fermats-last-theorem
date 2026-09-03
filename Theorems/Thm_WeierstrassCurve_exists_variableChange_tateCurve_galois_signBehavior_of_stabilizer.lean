import Mathlib
import Definitions.Def_TateCurve_TateParameter
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in
theorem WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ)
    (hstab : ∀ D : VariableChange (AlgebraicClosure ℚ_[p]),
        D • ((TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) →
        D = 1 ∨ D = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p]))) :
    ∃ (d : ℚ_[p]), ‖d‖₊ = 1 ∧
      ∃ (s : AlgebraicClosure ℚ_[p]), s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d ∧
        ∃ C : VariableChange (AlgebraicClosure ℚ_[p]),
          C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
            = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) ∧
          ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
            (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
            (σ s ≠ s → C.map σ.toAlgHom.toRingHom
              = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer.solution
