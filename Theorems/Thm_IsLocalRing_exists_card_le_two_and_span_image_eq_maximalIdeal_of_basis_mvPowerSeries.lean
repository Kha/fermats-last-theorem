import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries

set_option autoImplicit false

theorem IsLocalRing.exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries
    {κ : Type} [Field κ] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra R (MvPowerSeries (Fin 2) κ)]
    {ι : Type} [Fintype ι] (b : Module.Basis ι R (MvPowerSeries (Fin 2) κ))
    {m : ℕ} (s : Fin m → R) (hs : Ideal.span (Set.range s) = IsLocalRing.maximalIdeal R) :
    ∃ t : Finset (Fin m), t.card ≤ 2 ∧
      Ideal.span (s '' (t : Set (Fin m))) = IsLocalRing.maximalIdeal R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_card_le_two_and_span_image_eq_maximalIdeal_of_basis_mvPowerSeries.solution
