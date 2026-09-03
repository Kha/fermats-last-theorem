import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) [IsSeparated y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Algebra.Etale R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y)
    (ha : a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶
      pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))))
    (hτ₁ : τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) =
      pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (hτ₂ : ∀ {T : Scheme.{u}}
        (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
        (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
      v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
      v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
      x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (V : (pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).Opens)
      (G : SchemeHomOver (V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'),
      (∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (U : Scheme.{u}))
          (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.fst y y →
        s ≫ V.ι ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.snd y y →
        v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
        v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
            pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        s ≫ G.1 = v ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'')) (w₁ w₂ : T ⟶ (U : Scheme.{u}))
          (s : T ⟶ pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))),
        w₁ ≫ U.ι ≫ pullback.fst y y = t ≫ a →
        w₂ ≫ U.ι ≫ pullback.fst y y = w₁ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₁ ≫ m.1 →
        s ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₂ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          t ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
        Set.range s.base ⊆ (V : Set ↑(pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
          (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))))) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.solution
