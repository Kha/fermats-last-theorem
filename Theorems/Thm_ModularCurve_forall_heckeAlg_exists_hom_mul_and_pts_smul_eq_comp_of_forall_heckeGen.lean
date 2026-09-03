import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
    (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)] (N : ℕ) [NeZero N]
    {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hgen : letI := heckeModuleBar N
      ∀ ℓ : Nat.Primes, ∃ φ : SchemeHomOver g g,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
        ∀ x : JZero N, (pts (heckeGen ℓ • x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar N
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero N, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen.solution
