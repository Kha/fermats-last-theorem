import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong

set_option autoImplicit false

open KaehlerDifferential AlgebraicCurve

theorem AlgebraicCurve.sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong
    {K F R : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
    [HasPrincipalDivisors K R] [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K R]
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K R, w.DCoordGenerates] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[R⁄K]]
    (α β : F →ₐ[K] R) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFα : FibreResidueIdentityAlong α hα) (hFβ : FibreResidueIdentityAlong β hβ) (hsep : SeparableAlong K β)
    (hΩ : ∀ η : Ω[R⁄K], ∃ (ω₁ : Ω[F⁄K]) (c : R), η = c • Differential.pullbackAlong β ω₁)
    (S : Finset (Place K F))
    (hS : ∀ w : Place K R, Place.restrictAlong α hα w ∈ S ↔ Place.restrictAlong β hβ w ∈ S)
    (g : F) (u : R) (ω : Ω[F⁄K]) :
    ∑ x ∈ S, kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong α (β g * u))) x
      = ∑ z ∈ S, kaehlerResidueTerm (Differential.traceAlong β (u • Differential.pullbackAlong α ω)) (diagonalHom K F g) z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_sum_kaehlerResidueTerm_traceFunAlong_mul_eq_sum_kaehlerResidueTerm_traceAlong_smul_pullbackAlong.solution
