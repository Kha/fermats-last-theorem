import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre

universe u

open CategoryTheory

theorem GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    {t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)}
    [AlgebraicGeometry.IsSeparated f] [AlgebraicGeometry.Flat t]
    (G : GoodReductionJacobian.RelativeGroupLaw R f) (H : GoodReductionJacobian.RelativeGroupLaw R t)
    (φ : NeronModelInfra.SchemeHomOver t f)
    (hφ : ∀ {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
        (x y : NeronModelInfra.SchemeHomOver (s ≫ NeronModelInfra.specGenericFibreInclusion R K) t),
        (H.mul _ x y).1 ≫ φ.1 =
          (G.mul _ ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
            ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1)
    {S : AlgebraicGeometry.Scheme.{u}} (s : S ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    (x y : NeronModelInfra.SchemeHomOver s t) :
    (H.mul s x y).1 ≫ φ.1 =
      (G.mul s ⟨x.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, x.2]⟩
        ⟨y.1 ≫ φ.1, by rw [CategoryTheory.Category.assoc, φ.2, y.2]⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre.solution
