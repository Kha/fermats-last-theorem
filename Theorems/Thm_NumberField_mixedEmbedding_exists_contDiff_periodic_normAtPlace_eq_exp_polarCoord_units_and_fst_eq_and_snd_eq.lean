import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq
    (K : Type) [Field K] [NumberField K] :
    ∃ (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
          (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
      (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
      (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ)),
      (∀ s, ContDiff ℝ (⊤ : ℕ∞) (P s)) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (k : Fin (nrComplexPlaces K) → ℤ), P s (x, θ + fun j => (k j : ℝ)) = P s (x, θ)) ∧
      (∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
          P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ')) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
          normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ))) ∧
      (∀ y : mixedSpace K, IsUnit y →
          P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
              Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) ∧
      (∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
          sgn (y * y') = sgn y * sgn y' ∧
            ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ)) ∧
      (∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
          ∃ R : ℝ, ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
            P s (x, θ) ∈ C → ∀ i, |x i| ≤ R) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsReal}),
          (P s (x, θ)).1 w = (((s w : ℤˣ) : ℤ) : ℝ) * Real.exp (x (Fintype.equivFin (InfinitePlace K) w.1))) ∧
      (∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
          (w : {w : InfinitePlace K // w.IsComplex}),
          (P s (x, θ)).2 w = Complex.exp (((x (Fintype.equivFin (InfinitePlace K) w.1) / 2 : ℝ) : ℂ) +
            2 * Real.pi * Complex.I * ((θ (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) : ℂ))) ∧
      (∀ (y : mixedSpace K) (w : {w : InfinitePlace K // w.IsReal}), sgn y w = if 0 < y.1 w then 1 else -1) ∧
      (∀ (y : mixedSpace K) (j : Fin (nrComplexPlaces K)),
          arg y j = Complex.arg (y.2 ((Fintype.equivFin {w : InfinitePlace K // w.IsComplex}).symm j)) / (2 * Real.pi)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_normAtPlace_eq_exp_polarCoord_units_and_fst_eq_and_snd_eq.solution
