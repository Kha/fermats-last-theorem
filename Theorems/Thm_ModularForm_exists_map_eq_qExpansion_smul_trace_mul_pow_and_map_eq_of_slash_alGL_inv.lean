import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))]
    {R₀ : Type*} [CommRing R₀] (φ : R₀ →+* ℂ) (I : Ideal R₀) (hpI : ((p : ℕ) : R₀) ∈ I)
    {k₁ k₂ : ℤ} (g gW : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k₁)
    (ε εW : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hgW : (⇑gW : UpperHalfPlane → ℂ) = (⇑g : UpperHalfPlane → ℂ) ∣[k₁] W.alGL⁻¹)
    (hεW : (⇑εW : UpperHalfPlane → ℂ) = (⇑ε : UpperHalfPlane → ℂ) ∣[k₂] W.alGL⁻¹)
    (u v s t : R₀) (c e : ℕ) (Pg PgW Pε PεW : PowerSeries R₀)
    (hg : Pg.map φ = φ u • UpperHalfPlane.qExpansion 1 (⇑g : UpperHalfPlane → ℂ))
    (hgW' : PgW.map φ = (φ v * (p : ℂ) ^ c) • UpperHalfPlane.qExpansion 1 (⇑gW : UpperHalfPlane → ℂ))
    (hε : Pε.map φ = φ s • UpperHalfPlane.qExpansion 1 (⇑ε : UpperHalfPlane → ℂ))
    (hεI : Pε.map (Ideal.Quotient.mk I) = PowerSeries.C (Ideal.Quotient.mk I t))
    (hεW' : ((p : ℂ) ^ e) • PεW.map φ = φ s • UpperHalfPlane.qExpansion 1 (⇑εW : UpperHalfPlane → ℂ))
    (i : ℕ) (hi : i + c < e * i) :
    ∃ P : PowerSeries R₀,
      P.map φ = UpperHalfPlane.qExpansion 1
        (φ (u * v * s ^ i) • (⇑(ModularForm.trace
          (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) : Subgroup (GL (Fin 2) ℝ))
          (g.mul (ε.pow i))) : UpperHalfPlane → ℂ)) ∧
      P.map (Ideal.Quotient.mk I) = (PowerSeries.C (v * t ^ i) * Pg).map (Ideal.Quotient.mk I) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv.solution
