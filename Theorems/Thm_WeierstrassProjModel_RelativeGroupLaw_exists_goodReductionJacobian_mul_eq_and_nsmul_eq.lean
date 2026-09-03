import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra

theorem WeierstrassProjModel.RelativeGroupLaw.exists_goodReductionJacobian_mul_eq_and_nsmul_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) :
    ∃ G' : GoodReductionJacobian.RelativeGroupLaw R f,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), G'.mul t x y = G.mul t x y) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), G'.one t = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), G'.inv t x = G.inv t x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f),
        G'.nsmul t n x = G.nsmul t n x) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq.solution
