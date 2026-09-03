import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
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
    ∃ φ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p
          ≃+ Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
      ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, φ (σ • P) = σ • φ P) ∧
        (σ s ≠ s → ∀ P, φ (σ • P) = -(σ • φ P)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior.solution
