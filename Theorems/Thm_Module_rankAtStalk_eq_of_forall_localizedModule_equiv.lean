import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import P2M.Util
import P2M.Sol.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv

set_option autoImplicit false

universe u

theorem Module.rankAtStalk_eq_of_forall_localizedModule_equiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite R N] [Module.Flat R N] (s : Set A) (hs : Ideal.span s = ⊤)
    (H : ∀ h ∈ s, Nonempty
      (LocalizedModule (Submonoid.powers h) M ≃ₗ[A] LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk N := by p2m_exact_reverting @_root_.P2MW.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv.solution
