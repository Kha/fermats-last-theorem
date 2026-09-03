import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.sgn_eq_one_of_forall_pos_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
      (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (hP_cont : ∀ s, Continuous (P s))
    (hP_mul : ∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ'))
    (hP_norm : ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
      normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ)))
    (hP_inv : ∀ y : mixedSpace K, IsUnit y →
      P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) :
    ∀ y : mixedSpace K, IsUnit y → (∀ w : {w : InfinitePlace K // w.IsReal}, 0 < y.1 w) → sgn y = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord.solution
