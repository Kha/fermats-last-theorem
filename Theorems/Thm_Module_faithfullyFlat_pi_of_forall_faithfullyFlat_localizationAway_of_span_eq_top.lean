import Mathlib
import P2M.Util
import P2M.Sol.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top

set_option autoImplicit false

universe u

theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i) := by p2m_exact_reverting @_root_.P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top.solution
