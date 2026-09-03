import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (hd : ¬ ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 = d.1) :
    IsClosedImmersion
      (pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).1
        (pullback.condition.trans
          (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R K)))
            ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
            (GoodReductionJacobian.schemeHomOverComp
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).2.symm) :
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback f f) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section.solution
