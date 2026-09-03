import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_Etale_isPushout_frobenius

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem RingHom.Etale.isPushout_frobenius
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_Etale_isPushout_frobenius.solution
