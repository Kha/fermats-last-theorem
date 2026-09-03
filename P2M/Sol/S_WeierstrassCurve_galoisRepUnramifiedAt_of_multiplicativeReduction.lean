import Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import P2M.Util
namespace P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℤ) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q)
    (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hv : ℓ ∣ padicValInt q W.Δ) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) ℓ q := by
  intro A hA σ hσ x

  obtain ⟨M, hmem, -, hfix⟩ :=
    W.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction hq hΔ hqΔ hqc₄ A hA hℓ
  have hM : ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, ℓ • P = 0 →
        W.InZeroComponentAt A P → τ • P = P := by
    intro τ hτ P hP hP0
    have hPmem : P ∈ Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ := by
      rw [Submodule.mem_torsionBy_iff]
      simpa [natCast_zsmul] using hP
    have h := hfix hℓq τ hτ ⟨P, hPmem⟩ ((hmem ⟨P, hPmem⟩).mpr hP0)
    exact congrArg Subtype.val h
  by_cases hx : W.InZeroComponentAt A (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
  · exact hfix hℓq σ hσ x ((hmem x).mpr hx)
  · apply Subtype.ext
    have hxP : ℓ • (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
      have hx' := x.property
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hx'
      exact hx'
    exact W.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd hq hℓ hℓq hΔ hqΔ hqc₄ hv A hA
      hM σ hσ _ hxP hx
