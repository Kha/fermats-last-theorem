import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_natCast_smul_of_forall_add_eq_mul
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (W : Type) [AddCommGroup W] [Module k W]
    (τ : W → SchemeHomOver (tangentBase k sk) f)
    (hadd : ∀ v w : W, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (n : ℕ) (w : W) :
    L.nsmul (tangentBase k sk) n (τ w) = τ ((n : k) • w) ∧
      ((n : k) = 0 → L.nsmul (tangentBase k sk) n (τ w) = L.one (tangentBase k sk)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul.solution
