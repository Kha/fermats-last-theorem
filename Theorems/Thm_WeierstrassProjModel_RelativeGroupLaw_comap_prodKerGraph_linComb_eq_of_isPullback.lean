import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.comap_prodKerGraph_linComb_eq_of_isPullback
    {B T : Type u} [CommRing B] [CommRing T] (f : B →+* T)
    {E E' : Scheme.{u}} (p : E ⟶ Spec (CommRingCat.of B)) (p' : E' ⟶ Spec (CommRingCat.of T))
    [IsSeparated p] [IsSeparated p'] (π : E' ⟶ E)
    (hP : IsPullback π p' p (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw B p) (L : RelativeGroupLaw T p')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver s p'),
      (L.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (q : ℕ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) p')
    (hPp : (P.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f))
    (hQp : (Q.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)) :
    Scheme.IdealSheafData.comap
      (prodKerGraph p
        (fun i : Fin (q * q) ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).1)
        (fun i ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).2))
      (pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hP.w, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      prodKerGraph p'
        (fun i : Fin (q * q) ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).1)
        (fun i ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).2) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback.solution
