import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_polynomial

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_toLaurent_comp_eq_of_isProper~exists_eq_snd_comp_of_comp_eq_const_of_isProper~exists_isProper_twoAffineLineCover NeronModelInfra GoodReductionJacobian"

universe u
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_polynomial
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f)
    (ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ A)
    (hψ : ψ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      ψ = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ≫ a := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_polynomial.solution
