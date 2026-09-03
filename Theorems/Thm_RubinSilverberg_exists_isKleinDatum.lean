import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_RubinSilverberg_exists_isKleinDatum

open RubinSilverberg
theorem RubinSilverberg.exists_isKleinDatum {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] (a b : K) (hD : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : ∃ u₀ : K, RubinSilverberg.IsKleinDatum a b u₀ := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_exists_isKleinDatum.solution
