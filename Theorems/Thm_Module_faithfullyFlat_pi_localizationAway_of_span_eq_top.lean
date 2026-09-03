import Mathlib
import P2M.Util
import P2M.Sol.S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top

set_option autoImplicit false

universe u

theorem Module.faithfullyFlat_pi_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) := by p2m_exact_reverting @_root_.P2MW.S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top.solution
