import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~genericFibreRestrict_injective_of_flat_of_isSeparated GoodReductionJacobian"

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_glued_charts_mul_eq
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hL : L.IsCommutative)
    [Flat f] [IsSeparated f]
    {Φ : Type u} [AddCommGroup Φ]
    (y : Φ → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (c : Φ → Φ → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hc : ∀ φ ψ, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ (c φ ψ).1 =
      (L.mul _ (L.mul _ (y φ) (y ψ)) (L.inv _ (y (φ + ψ)))).1)
    (hc0 : c 0 0 = L.one _)
    {N : Scheme.{u}} (gN : N ⟶ Spec (CommRingCat.of R)) [IsSeparated gN]
    (e : Φ → (G ⟶ N)) (he : ∀ φ, IsOpenImmersion (e φ)) (hef : ∀ φ, e φ ≫ gN = f)
    (hecov : (⋃ φ, Set.range (e φ).base) = Set.univ)
    (t : Φ → Φ → (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (ht : ∀ φ ψ, (t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl
            (L.mul _ (y φ) (L.inv _ (y ψ))))).1)
    (hpb : ∀ φ ψ, φ ≠ ψ →
      IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        ((t φ ψ).hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e φ) (e ψ)) :
    ∃ LN : RelativeGroupLaw R gN, LN.IsCommutative ∧
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (φ ψ : Φ) (a b : SchemeHomOver s f),
        LN.mul s (NeronModelInfra.schemeHomOverComp a ⟨e φ, hef φ⟩)
            (NeronModelInfra.schemeHomOverComp b ⟨e ψ, hef ψ⟩) =
          NeronModelInfra.schemeHomOverComp
            (L.mul s (L.mul s a b) (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) (c φ ψ)))
            ⟨e (φ + ψ), hef (φ + ψ)⟩ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_glued_charts_mul_eq.solution
