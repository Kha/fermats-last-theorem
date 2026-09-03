import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet_of_not_dvd
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve hiding pow_q_sq_eq_self_of_mem_ssJSet open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]

    (h4 : ∀ (𝔮 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))) [𝔮.IsPrime],
      (∃ a ∈ ssJSet p κ, (1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p -
          a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : ↥(chartAlgFin (N * p) p)) ∈ 𝔮) →
      ∀ 𝔭 ∈ minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)), 𝔭 ≤ 𝔮)

    (y : Ideal ↥(chartAlgFin (N * p) p)) [y.IsPrime] (hyp : ((p : ℕ) : ↥(chartAlgFin (N * p) p)) ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin (N * p) p) →+* Ω), RingHom.ker φ = y → φ (jChartFin (N * p) p) ∈ ssJSet p Ω) :
    ∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes, 𝔭 ≤ y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_forall_minimalPrimes_span_natCast_le_of_forall_apply_jChartFin_mem_ssJSet_of_not_dvd.solution
