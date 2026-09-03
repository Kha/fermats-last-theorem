import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ)
    (hdeg : ∀ E : Divisor K F, E ∈ Divisor.degZero (K := K) (F := F) →
      Divisor.correspondence φ ψ hφ hψ E ∈ Divisor.degZero (K := K) (F := F))
    (Tbar : Pic0 K F →+ Pic0 K F)
    (hTbar : ∀ E : Divisor.degZero (K := K) (F := F),
      Tbar (Pic0.mk E) = Pic0.mk ⟨Divisor.correspondence φ ψ hφ hψ E, hdeg E E.2⟩)
    (p : ℕ) (δ : Pic0.torsion K F p →+ Ω[F⁄K])
    (hδ : ∀ (y : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (y : Pic0 K F) → g ≠ 0 →
        (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K F g)
    (x y : Pic0.torsion K F p) (hy : (y : Pic0 K F) = Tbar x) :
    δ y = Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by
  obtain ⟨D, f, hDx, hf0, -, hord⟩ := Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (x := (x : Pic0 K F)) x.2
  have hD : ∀ v : Place K F, (p : ℤ) * (D : Divisor K F) v = v.ord f := fun v => (hord v).symm
  obtain ⟨g, -, hg0, hcorr, hdlog⟩ :=
    Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong K F F' φ ψ hφ hψ
      hfin hN hsep p D f hf0 hD
  have hx : δ x = f⁻¹ • KaehlerDifferential.D K F f := hδ x D f hDx hf0 hD
  have hyE : Pic0.mk ⟨Divisor.correspondence φ ψ hφ hψ D, hdeg D D.2⟩ = (y : Pic0 K F) := by
    rw [hy, ← hDx, hTbar]
  have hyv : δ y = g⁻¹ • KaehlerDifferential.D K F g := hδ y _ g hyE hg0 hcorr
  rw [hyv, hdlog, hx]
