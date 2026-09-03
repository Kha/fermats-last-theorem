import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
import P2M.Util
namespace P2MW.S_WeierstrassCurve_exists_addEquiv_torsion_tateCurve_signTwist_of_tateParameter
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (hj : (TateCurve.curve qT).c₄ ^ 3
        = (((W.map (Int.castRingHom ℚ)).c₄ ^ 3 / (W.map (Int.castRingHom ℚ)).Δ : ℚ) : ℚ_[p])
            * (TateCurve.curve qT).Δ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ (d : ℚ_[p]), ‖d‖₊ = 1 ∧
      ∃ (s : AlgebraicClosure ℚ_[p]), s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d ∧
        ∃ φ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p
              ≃+ Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p,
          ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
            (σ s = s → ∀ P, φ (σ • P) = σ • φ P) ∧
            (σ s ≠ s → ∀ P, φ (σ • P) = -(σ • φ P)) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  obtain ⟨d, hd, s, hs, C, hC, hCσ⟩ :=
    WeierstrassCurve.exists_variableChange_tateCurve_algebraicClosure_galois_signBehavior
      W p hΔ hpΔ hpc₄ qT hqT0 hqT1 hj
  obtain ⟨φ, hφ⟩ :=
    WeierstrassCurve.exists_addEquiv_torsion_tateCurve_signTwist_of_variableChange_galois_signBehavior
      W p qT s C hC hCσ
  exact ⟨d, hd, s, hs, φ, hφ⟩
