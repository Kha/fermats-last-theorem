import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_compatible_linearMap_pair_mk_tmul_eq_smul

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (h₀ : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₀ x ≤ Q.N₀ y)
    (h₁ : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₁ x ≤ Q.N₁ y) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧
      ∃ (A₀ : latticeBaseChange 𝒪 K B (Q.L₀ x) →ₗ[B] Q.T₀) (A₁ : latticeBaseChange 𝒪 K B (Q.L₁ x) →ₗ[B] Q.T₁),
        (∀ w, A₁ (inclBaseChange B (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) w) = Q.Pi₀ (A₀ w)) ∧
        (∀ w, A₀ (((smulInto π (Q.smul_le x)).baseChange B :
            latticeBaseChange 𝒪 K B (Q.L₁ x) →ₗ[B] latticeBaseChange 𝒪 K B (Q.L₀ x)) w) = Q.Pi₁ (A₁ w)) ∧
        (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : ↥(Q.N₀ x),
          LocalizedModule.mk (A₀ ((1 : B) ⊗ₜ[𝒪] v)) 1 =
            algebraMap B (locRing B y) r • Q.u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, h₀ y hy v.2⟩ : ↥(Q.N₀ y)))) ∧
        (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : ↥(Q.N₁ x),
          LocalizedModule.mk (A₁ ((1 : B) ⊗ₜ[𝒪] v)) 1 =
            algebraMap B (locRing B y) r • Q.u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, h₁ y hy v.2⟩ : ↥(Q.N₁ y)))) ∧
        (∀ t : Q.T₀, ∃ (w : latticeBaseChange 𝒪 K B (Q.L₀ x)) (n : ℕ), A₀ w = r ^ n • t) ∧
        (∀ t : Q.T₁, ∃ (w : latticeBaseChange 𝒪 K B (Q.L₁ x)) (n : ℕ), A₁ w = r ^ n • t) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_compatible_linearMap_pair_mk_tmul_eq_smul.solution
