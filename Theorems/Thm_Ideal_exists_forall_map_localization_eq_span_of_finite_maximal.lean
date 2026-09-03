import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal

set_option autoImplicit false

universe u v

theorem Ideal.exists_forall_map_localization_eq_span_of_finite_maximal
    (P : Type u) [CommRing P] [IsNoetherianRing P] (J : Ideal P)
    (hfin : {𝔫 : Ideal P | 𝔫.IsMaximal ∧ J ≤ 𝔫}.Finite) (N : ℕ)
    (hloc : ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
      ∃ g : Fin N → P, (∀ i, g i ∈ J) ∧
        Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
          Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (g i))) :
    ∃ f : Fin N → P, (∀ i, f i ∈ J) ∧
      ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
        Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
          Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (f i)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_map_localization_eq_span_of_finite_maximal.solution
