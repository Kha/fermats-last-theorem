import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat

universe u

open TensorProduct

theorem RingHom.QuasiFinite.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
      (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat.solution
