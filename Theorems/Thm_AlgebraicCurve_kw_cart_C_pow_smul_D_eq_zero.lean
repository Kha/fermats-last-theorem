import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_kw_cart_C_pow_smul_D_eq_zero
attribute [-simp] AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

theorem AlgebraicCurve.kw_cart_C_pow_smul_D_eq_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F,
      IsSeparable (AlgebraicCurve.KwPke.kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (AlgebraicCurve.KwPke.kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (g : F) {i : ℕ} (hi : i + 1 < ℓ) :
    AlgebraicCurve.KwCart.kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ i • KaehlerDifferential.D K F g) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_kw_cart_C_pow_smul_D_eq_zero.solution
