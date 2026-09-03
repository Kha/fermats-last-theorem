import Mathlib
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow

open ModularCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.coeff_qExpansionDiffAlong_kw_cart_C_pow
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    (F : IntermediateField K (LaurentSeries K)) [CharP F p] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong F.val (kw_cart_C (K := K) t hdt hspan hsep hdeg ω)).coeff n ^ p
      = (qExpansionDiffAlong F.val ω).coeff (n * p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.solution
