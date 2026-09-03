import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (qT : ℚ_[p])
    (s : AlgebraicClosure ℚ_[p])
    (C : VariableChange (AlgebraicClosure ℚ_[p]))
    (hC : C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
    (hCσ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
        (σ s ≠ s → C.map σ.toAlgHom.toRingHom
          = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C)) :
    ∃ ψ : ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point
          ≃+ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point,
      ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, ψ (σ • P) = σ • ψ P) ∧
        (σ s ≠ s → ∀ P, ψ (σ • P) = -(σ • ψ P)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior.solution
