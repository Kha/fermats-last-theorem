import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_baseScalar_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (n : ℕ) (a : S) (s : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (GradedOAlgebra.baseScalar f a • s))
      = GradedOAlgebra.baseScalar f' (algebraMap S S' a) • ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) s) := by

  have key : c.appTop.hom (GradedOAlgebra.baseScalar f a) = GradedOAlgebra.baseScalar f' (algebraMap S S' a) := by
    simp only [GradedOAlgebra.baseScalar]
    have h1 : c.appTop.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a)) =
        (c ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) := by
      rw [Scheme.Hom.comp_appTop]; rfl
    rw [h1, hc.w, Scheme.Hom.comp_appTop]
    change f'.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a)) = _
    congr 1
    have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap S S'))
    have h3 := congrArg (fun φ => φ.hom a) h2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    exact h3.symm

  change ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
      (Scheme.Modules.pullbackLocalSection c (GradedOAlgebra.baseScalar f a • s)) =
    GradedOAlgebra.baseScalar f' (algebraMap S S' a) •
      ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
        (Scheme.Modules.pullbackLocalSection c s)
  rw [Scheme.Modules.pullbackLocalSection_smul]
  exact (Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom)
    (U := ⊤) (c.appTop.hom (GradedOAlgebra.baseScalar f a)) (Scheme.Modules.pullbackLocalSection c s)).trans (by rw [key])
