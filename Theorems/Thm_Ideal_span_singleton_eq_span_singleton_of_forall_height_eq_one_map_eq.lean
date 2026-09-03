import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq

set_option autoImplicit false

universe u

theorem Ideal.span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hprin : ∀ P : Ideal A, P.IsPrime → P.height = 1 → Submodule.IsPrincipal P)
    {g t : A} (hg : g ≠ 0) (ht : t ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {g}) =
        Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {t})) :
    Ideal.span ({g} : Set A) = Ideal.span {t} := by p2m_exact_reverting @_root_.P2MW.S_Ideal_span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq.solution
