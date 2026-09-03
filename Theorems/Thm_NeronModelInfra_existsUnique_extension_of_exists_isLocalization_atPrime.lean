import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [Flat t] [LocallyOfFiniteType t]
    (v : NeronModelInfra.SchemeHomOver (pullback.snd t (NeronModelInfra.specGenericFibreInclusion R K))
      (pullback.snd f (NeronModelInfra.specGenericFibreInclusion R K)))
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A K) (_ : IsScalarTower R A K)
        (gA : pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ X),
        gA ≫ f = pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ t ∧
        ∀ j : pullback t (NeronModelInfra.specGenericFibreInclusion R K) ⟶
            pullback t (Spec.map (CommRingCat.ofHom (algebraMap R A))),
          j ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R A))) =
            pullback.fst t (NeronModelInfra.specGenericFibreInclusion R K) →
          j ≫ gA = v.1 ≫ pullback.fst f (NeronModelInfra.specGenericFibreInclusion R K)) :
    ∃! φ : NeronModelInfra.SchemeHomOver t f, NeronModelInfra.genericFibreRestrict R K f t φ = v := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime.solution
