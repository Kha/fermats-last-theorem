import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum_iff_of_semilinear
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ₀ : Submodule.span B' (Set.range τ₀) = ⊤) (hτ₁ : Submodule.span B' (Set.range τ₁) = ⊤)
    (hPi₀ : ∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) (hPi₁ : ∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s))
    (x' : PrimeSpectrum B') :
    (x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀) ∧
      (x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear.solution
