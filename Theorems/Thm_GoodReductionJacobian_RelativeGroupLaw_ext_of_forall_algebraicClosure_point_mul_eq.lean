import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.ext_of_forall_algebraicClosure_point_mul_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar]
    [IsScalarTower R K Kbar]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)}
    [Smooth f] [IsSeparated f]
    (L₁ L₂ : RelativeGroupLaw R f)
    (hmul : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) f,
      L₁.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y =
        L₂.mul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) x y) :
    L₁ = L₂ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_ext_of_forall_algebraicClosure_point_mul_eq.solution
