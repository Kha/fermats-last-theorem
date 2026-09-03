import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id
    {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (B : Type u) [CommRing B] [Algebra k B] (i : Spec (CommRingCat.of B) ⟶ A)
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (𝔪 : Ideal B) [𝔪.IsMaximal] (χ : B →ₐ[k] k) (hχ : ∀ b : B, b ∈ 𝔪 ↔ χ b = 0) :
    ∃ (Φ : A ⟶ pullback (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪))),
      IsIso Φ ∧
      Φ ≫ pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.fst f (i ≫ f) = 𝟙 A ∧
      Φ ≫ pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.snd f (i ≫ f) =
        f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ∧
      Φ ≫ pullback.snd (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) =
        f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift 𝔪 χ.toRingHom (fun b hb => (hχ b).mp hb))) ∧
      ∀ N : (pullback f f).Modules,
        Nonempty ((Scheme.Modules.pullback Φ).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj
            ((Scheme.Modules.pullback
              (pullback.lift (pullback.fst f (i ≫ f)) (pullback.snd f (i ≫ f) ≫ i)
                (by rw [Category.assoc]; exact pullback.condition))).obj N)) ≅
          (Scheme.Modules.pullback
            (pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ i)
              (by rw [Category.id_comp, Category.assoc, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    show χ.toRingHom.comp (algebraMap k B) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
                    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]))).obj N) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id.solution
