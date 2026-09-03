import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws
attribute [-simp] AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

set_option autoImplicit false

open AlgebraicCurve.KwCart AlgebraicCurve.KwPke

theorem AlgebraicCurve.kw_cart_C_eq_of_cartierLaws {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K] [CharP F p]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ y : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield y)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (ω : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg ω = C ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws.solution
