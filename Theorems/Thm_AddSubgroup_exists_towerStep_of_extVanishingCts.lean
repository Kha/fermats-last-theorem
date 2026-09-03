import Mathlib
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_AddSubgroup_exists_towerStep_of_extVanishingCts
attribute [-instance] ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec
attribute [-simp] compl₂EDS_two

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem AddSubgroup.exists_towerStep_of_extVanishingCts
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hcard : ∀ k : ℕ, Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ k : ℕ) : ℤ))
      = p ^ (2 * k))
    (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m) (hK1 : IsAddCyclic K)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hKstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K, σ • x ∈ K)
    (hCof : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p • e = 0 → σ • e - e ∈ K)
    (hCyc : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x ∈ K, p • x = 0 → σ • x = ExtCitation.cycloExp p σ • x)
    (hU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p • y ∈ K → τ • y - y ∈ K)
    (hSp : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∃ F' : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F', σ • x ∈ F') ∧
        K ≤ F' ∧ (∀ x ∈ F', p • x ∈ K) ∧ Nat.card F' = p ^ (m + 1) ∧
        ∀ x ∈ F', ∀ e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
          p • e = 0 → x - e ∈ K → x ∈ K)
    (hEXT : ExtCitation.ExtVanishingCts p) :
    ∃ K' : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      K ≤ K' ∧
      Nat.card K' = p ^ (m + 1) ∧
      (∀ x ∈ K', p ^ (m + 1) • x = 0) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ K', σ • x ∈ K') ∧
      (∀ x ∈ K', p • x = 0 → x ∈ K) := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_exists_towerStep_of_extVanishingCts.solution
