import Mathlib
import P2M.Util
import P2M.Sol.S_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top

set_option autoImplicit false

theorem Localization.Away.existsUnique_forall_algebraMap_eq_of_span_eq_top
    {B : Type} [CommRing B] {n : ℕ} (g : Fin n → B) (hg : Ideal.span (Set.range g) = ⊤)
    (x : ∀ i : Fin n, Localization.Away (g i))
    (hx : ∀ i j : Fin n, IsLocalization.Away.awayToAwayRight (S := Localization.Away (g i)) (g i) (g j)
        (P := Localization.Away (g i * g j)) (x i) =
      IsLocalization.Away.awayToAwayLeft (S := Localization.Away (g j)) (g j) (g i)
        (P := Localization.Away (g i * g j)) (x j)) :
    ∃! b : B, ∀ i : Fin n, algebraMap B (Localization.Away (g i)) b = x i := by p2m_exact_reverting @_root_.P2MW.S_Localization_Away_existsUnique_forall_algebraMap_eq_of_span_eq_top.solution
