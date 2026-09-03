import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_exists_int_kleinVHom_ne_zero

open RubinSilverberg
theorem RubinSilverberg.exists_int_kleinVHom_ne_zero {K : Type*} [Field K] [CharZero K] (β γ u₀ : K) (hV : kleinV u₀ ≠ 0) : ∃ l : ℤ, kleinVHom (β + l * u₀) (γ + l) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_exists_int_kleinVHom_ne_zero.solution
