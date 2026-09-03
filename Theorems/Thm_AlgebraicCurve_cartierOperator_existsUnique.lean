import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_cartierOperator_existsUnique
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

set_option autoImplicit false

universe u v

theorem AlgebraicCurve.cartierOperator_existsUnique {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃! C : Ω[F⁄K] →+ Ω[F⁄K],
      (∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω) ∧
      (∀ f : F, C (KaehlerDifferential.D K F f) = 0) ∧
      (∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cartierOperator_existsUnique.solution
