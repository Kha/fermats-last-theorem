import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul

set_option autoImplicit false

universe u v

theorem Ideal.map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul
    {P : Type u} [CommRing P] [IsNoetherianRing P] (J : Ideal P) (𝔫 : Ideal P) [𝔫.IsPrime]
    {ι : Type v} (h : ι → P) (hh : ∀ i, h i ∈ J)
    (hle : J ≤ Ideal.span (Set.range h) ⊔ 𝔫 * J) :
    Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
      Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (h i)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul.solution
