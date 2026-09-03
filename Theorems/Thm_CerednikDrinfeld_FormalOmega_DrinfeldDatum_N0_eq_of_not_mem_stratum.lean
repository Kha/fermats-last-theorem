import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N0_eq_of_not_mem_stratum

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.N0_eq_of_not_mem_stratum
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B) :
    (x ∉ Q.stratum₁ → ∀ v, v ∈ Q.N₀ x ↔ ∃ w ∈ Q.N₁ x, v = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w) ∧
    (x ∉ Q.stratum₀ → Q.N₀ x = Q.N₁ x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N0_eq_of_not_mem_stratum.solution
