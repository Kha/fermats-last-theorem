import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_p_dvd_padicValRat_freyCurve_discr

theorem FreyPackage.p_dvd_padicValRat_freyCurve_discr (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (P.p : ℤ) ∣ padicValRat ℓ P.freyCurve.Δ := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_p_dvd_padicValRat_freyCurve_discr.solution
