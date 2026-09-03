import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D

set_option autoImplicit false

theorem RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    {A S : Type} [CommRing A] [CommRing S] (i : A →+* S) (hi : i.FormallySmooth) (t : S)
    (hdt : letI : Algebra A S := i.toAlgebra;
      ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified := by p2m_exact_reverting @_root_.P2MW.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D.solution
