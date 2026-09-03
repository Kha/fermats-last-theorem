import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq

set_option autoImplicit false

universe u v

theorem Ideal.exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq
    (P : Type u) [CommRing P] [IsNoetherianRing P] (I J : Ideal P) (hIJ : I ≤ J)
    (hloc : ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
      Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J = Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) I) :
    ∃ e : P ⧸ I, IsIdempotentElem e ∧ Ideal.map (Ideal.Quotient.mk I) J = Ideal.span {e} := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq.solution
