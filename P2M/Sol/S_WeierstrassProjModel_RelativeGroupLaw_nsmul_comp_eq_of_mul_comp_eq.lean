import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_nsmul_comp_eq_of_mul_comp_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (f' : A' ⟶ Spec (CommRingCat.of R'))
    (π : A' ⟶ A) (hP : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R' f')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver s f'),
      (G'.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom g))
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (hone : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')),
      (G'.one s).1 ≫ π = (G.one (s ≫ Spec.map (CommRingCat.ofHom g))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver s f') :
    (G'.nsmul s n x).1 ≫ π =
      (G.nsmul (s ≫ Spec.map (CommRingCat.ofHom g)) n
        ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩).1 := by
  induction n with
  | zero => exact hone s
  | succ n ih =>
      show (G'.mul s (G'.nsmul s n x) x).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom g)) (G.nsmul (s ≫ Spec.map (CommRingCat.ofHom g)) n
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩)
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩).1
      rw [hmul]
      congr 2
      exact Subtype.ext ih
