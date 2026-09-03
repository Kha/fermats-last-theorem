import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed
set_option autoImplicit false
universe u v

theorem AlgebraicCurve.exists_dlog_of_cartierOperator_fixed {K : Type u} {F : Type v}
    [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (w : Ω[F⁄K]) (hfix : C w = w) :
    ∃ h : F, h ≠ 0 ∧ w = h⁻¹ • KaehlerDifferential.D K F h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed.solution
