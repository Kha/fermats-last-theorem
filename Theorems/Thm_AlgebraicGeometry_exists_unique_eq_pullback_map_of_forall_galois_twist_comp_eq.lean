import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
    (k K : Type) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X Y : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [IsSeparated fY] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))

    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))

    (hgal : ∀ (σ : K ≃ₐ[k] K)
      (hσ : Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 X) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ f =
        f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (𝟙 Y) (Spec.map (CommRingCat.ofHom ((σ : K →ₐ[k] K) : K →+* K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ])) :
    ∃ g : X ⟶ Y, ∃ hg : g ≫ fY = fX,
      f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, Category.id_comp]) ∧
      ∀ (g' : X ⟶ Y) (hg' : g' ≫ fY = fX),
        f = pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
              g' (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg']) (by rw [Category.comp_id, Category.id_comp]) →
        g' = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq.solution
