import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace

universe u v

open IsLocalRing

theorem IsRegularLocalRing.spanFinrank_ker_add_finrank_cotangentSpace {P : Type u} {S : Type v}
    [CommRing P] [IsLocalRing P] [IsNoetherianRing P] [CommRing S] [IsRegularLocalRing S]
    (f : P →+* S) (hf : Function.Surjective f) :
    (RingHom.ker f).spanFinrank + Module.finrank (ResidueField S) (CotangentSpace S) =
      Module.finrank (ResidueField P) (CotangentSpace P) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_spanFinrank_ker_add_finrank_cotangentSpace.solution
