import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (x' : PrimeSpectrum B')
    (h₀ : Q.N₀ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₀ x')
    (h₁ : Q.N₁ (DrinfeldDatum.pointUnder f x') ≤ Q'.N₁ x')
    (hs₀ : x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀)
    (hs₁ : x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁)
    (hcov : x' ∈ Q'.stratum₀ ∨ x' ∈ Q'.stratum₁) :
    Q'.N₀ x' = Q.N₀ (DrinfeldDatum.pointUnder f x') ∧ Q'.N₁ x' = Q.N₁ (DrinfeldDatum.pointUnder f x') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N_eq_of_le_of_mem_stratum_iff.solution
