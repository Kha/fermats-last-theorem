import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_algebraTower_of_mul_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [IsSeparated f]
    (F : Type u) [Field F] [Algebra R F]
    (K : Type u) [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    (G₀ G₁ : WeierstrassProjModel.RelativeGroupLaw R f)
    (hK : ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f,
        G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q
          = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q) :
    ∀ P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f,
      G₀.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q
        = G₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_algebraTower_of_mul_eq.solution
