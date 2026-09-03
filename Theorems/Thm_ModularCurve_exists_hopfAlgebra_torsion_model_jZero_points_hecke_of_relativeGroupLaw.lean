import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt p) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (hpts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (φJ : HeckeAlg → SchemeHomOver f f)
    (hφJ_mul : ∀ (t : HeckeAlg) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (φJ t) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (φJ t))
          (NeronModelInfra.schemeHomOverComp y (φJ t)))
    (hφJ_pts : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (x : JZero N), (pts (t • x)).1 = (pts x).1 ≫ (φJ t).1)
    (hfin : IsFinite (L.schemeNsmul p)) (hflat : Flat (L.schemeNsmul p)) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H),
      Module.Finite ↥(GaloisRep.ratLocalizedAt p) H ∧ Module.Flat ↥(GaloisRep.ratLocalizedAt p) H ∧ Coalgebra.IsCocomm ↥(GaloisRep.ratLocalizedAt p) H ∧
      ∃ (eT : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
          WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) ≃
            L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p)
        (e : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
        (φ : HeckeAlg → (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] H)),

        (∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (g * h)).val : SchemeHomOver _ f) = L.mul _ (eT T g).val (eT T h).val) ∧

        (∀ (T T' : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] [CommRing T'] [Algebra ↥(GaloisRep.ratLocalizedAt p) T']
            (u : T →ₐ[↥(GaloisRep.ratLocalizedAt p)] T') (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T' (.toConv (u.comp g.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom u.toRingHom) ≫ (eT T g).val.1) ∧

        (∀ g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ),
          pts (e g : JZero N) = (eT (AlgebraicClosure ℚ) g).val) ∧

        (∀ g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ), e (g * h) = e g + e h) ∧

        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = σ (g x)) → ((e h : JZero N)) = σ • (e g : JZero N)) ∧

        (∀ t : HeckeAlg,
          RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H) ≤
            (RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H)).comap (φ t)) ∧

        (∀ (t : HeckeAlg) (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (.toConv (g.ofConv.comp (φ t)))).val : SchemeHomOver _ f).1 =
            (eT T g).val.1 ≫ (φJ t).1) ∧

        (∀ (t : HeckeAlg) (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = g (φ t x)) → ((e h : JZero N)) = t • (e g : JZero N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw.solution
