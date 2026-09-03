import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence
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
    δ y = Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_torsion_apply_eq_traceAlong_pullbackAlong_of_correspondence.solution
