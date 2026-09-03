import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (hG : G.IsCommutative)
    {σ : Type v} {J : Type w} [AddCommGroup J] [Module (MvPolynomial σ ℤ) J]
    {T₀ : Scheme.{u}} {s₀ : T₀ ⟶ Spec (CommRingCat.of R)} (pts : J → SchemeHomOver s₀ f)
    (hpts : ∀ x y : J, pts (x + y) = G.mul s₀ (pts x) (pts y))
    (hX : ∀ i : σ, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (G.mul s x y) φ =
          G.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : J, (pts ((MvPolynomial.X i : MvPolynomial σ ℤ) • x)).1 = (pts x).1 ≫ φ.1) :
    ∀ t : MvPolynomial σ ℤ, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (G.mul s x y) φ =
          G.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : J, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X.solution
