import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.Algebra.Category.CommBialgCat
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_hopfAlgebra_of_grpObj_over_spec

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u
theorem AlgebraicGeometry.exists_hopfAlgebra_of_grpObj_over_spec (R : Type u) [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [IsFinite G.hom] :
    ∃ (A : Type u) (_ : CommRing A) (_ : HopfAlgebra R A),
      Module.Finite R A ∧ Coalgebra.IsCocomm R A ∧
      ∃ e : ∀ (L : Type u) [CommRing L] [Algebra R L],
          WithConv (A →ₐ[R] L) ≃ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ G),
        (∀ (L : Type u) [CommRing L] [Algebra R L], ∀ (φ ψ : WithConv (A →ₐ[R] L)),
            e L (φ * ψ) = e L φ * e L ψ) ∧
        (∀ (L L' : Type u) [CommRing L] [Algebra R L] [CommRing L'] [Algebra R L'],
          ∀ (g : L →ₐ[R] L') (φ : WithConv (A →ₐ[R] L)),
            (e L' (.toConv (g.comp φ.ofConv))).left =
              Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e L φ).left) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_hopfAlgebra_of_grpObj_over_spec.solution
