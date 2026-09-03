import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_shortExact_map_ihom_of_free

set_option autoImplicit false

open CategoryTheory
theorem Rep.shortExact_map_ihom_of_free {G : Type} [Group G] (V : Type) [AddCommGroup V] [Module.Free ℤ V]
    (ρ : Representation ℤ G V) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) :
    (X.map (ihom (Rep.of ρ))).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_ihom_of_free.solution
