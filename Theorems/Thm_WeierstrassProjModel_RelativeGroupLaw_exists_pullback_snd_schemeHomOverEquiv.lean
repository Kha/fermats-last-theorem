import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
theorem WeierstrassProjModel.RelativeGroupLaw.exists_pullback_snd_schemeHomOverEquiv
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [CommRing K] [Algebra R K] :
    ∃ σ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f ≃
          SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∀ (G : WeierstrassProjModel.RelativeGroupLaw R f),
        ∃ G' : WeierstrassProjModel.RelativeGroupLaw K
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          (∀ P Q, σ (G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q)
            = G'.mul (𝟙 _) (σ P) (σ Q))
          ∧ σ (G.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = G'.one (𝟙 _) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv.solution
