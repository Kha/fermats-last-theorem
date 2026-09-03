import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ 𝒱 : (IgusaScheme N ℓ).TwoAffineOpenCover, 𝒱.U0 = chartFinOpen N ℓ ∧ 𝒱.U1 = chartInfOpen N ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen.solution
