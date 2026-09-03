import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y') [IsOpenImmersion ι.1]
    (hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base)
    (hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)))
    (hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1)
    (hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1)
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Module.FaithfullyFlat R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R R''))) :
    ∃ (Y'' : Scheme.{u}) (y'' : Y'' ⟶ Spec (CommRingCat.of R''))
      (ι₂ : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y'')
      (U'' : (pullback y'' y'').Opens) (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
      Smooth y'' ∧ IsSeparated y'' ∧ LocallyOfFiniteType y'' ∧ QuasiCompact y'' ∧
      IsOpenImmersion ι₂.1 ∧
      (∀ p : Y'', y''.base p ≠ IsLocalRing.closedPoint R'' → p ∈ Set.range ι₂.1.base) ∧
      (∀ p : Y'', (∀ p' : Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) → p ∈ Set.range ι₂.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y'')),
        u.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        p.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.snd y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R''))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
          w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) a).1 ≫ ι₂.1 ∧
          w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) b).1 ≫ ι₂.1 ∧
          w'.1 ≫ m''.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) c).1 ≫ ι₂.1) ∧
      (∃ a'' : Spec (CommRingCat.of R'') ⟶ Y'', a'' ≫ y'' = 𝟙 _) ∧
      (∃ j : pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ⟶ Y'',
        IsOpenImmersion j ∧ j ≫ y'' = pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
          (x₁ : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (x₂ : T ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R'')))),
          x₁ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₁ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' R'')) →
          x₂ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x₁ ≫ ι.1 →
          x₂ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₂ ≫ j = x ≫ ι₂.1) ∧
      (∃ (D : (pullback y'' y'').Opens) (hle : U'' ≤ D)
        (M : SchemeHomOver (D.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
        (pullback y'' y'').homOfLE hle ≫ M.1 = m''.1 ∧
        ∀ (a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))),
          a₂ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = a → a₂ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = 𝟙 _ →
          ∀ {T : Scheme.{u}} (b : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (q : T ⟶ pullback y'' y''),
            q ≫ pullback.fst y'' y'' = b ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 →
            q ≫ pullback.snd y'' y'' = b ≫ ι₂.1 →
            Set.range q.base ⊆ (D : Set ↑(pullback y'' y''))) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.solution
