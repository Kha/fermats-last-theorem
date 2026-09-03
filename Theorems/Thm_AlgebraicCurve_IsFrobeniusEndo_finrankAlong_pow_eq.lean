import Mathlib
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsFrobeniusEndo_finrankAlong_pow_eq

set_option autoImplicit false

theorem AlgebraicCurve.IsFrobeniusEndo.finrankAlong_pow_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hF : ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F)
    {φ : F →ₐ[K] F} {r : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo (p ^ r) φ) (n : ℕ) :
    AlgebraicCurve.finrankAlong K (φ ^ n) = (p ^ r) ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsFrobeniusEndo_finrankAlong_pow_eq.solution
