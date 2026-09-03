import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong

set_option autoImplicit false
theorem GaloisRepAdic.isEquiv_baseChangeAlong_baseChangeAlong
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (hf : IsLocalHom f) (g : B →+* C) (hg : IsLocalHom g) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong f hf).baseChangeAlong g hg).IsEquiv
      (ρ.baseChangeAlong (g.comp f) (RingHom.isLocalHom_comp g f)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong.solution
