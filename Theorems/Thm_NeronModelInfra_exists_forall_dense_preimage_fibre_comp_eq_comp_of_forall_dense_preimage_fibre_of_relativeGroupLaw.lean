import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :
    ∃ (UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens)
      (mY : SchemeHomOver (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f))),
        u.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        p.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ mY.1 →
        p.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ mY.1 →
        p.1 ≫ mY.1 = q.1 ≫ mY.1) ∧
      (∀ q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)),
        (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R → q ∈ UY) ∧
      (∀ {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u})),
        a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f → b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f →
        ∃ v : T ⟶ (UY : Scheme.{u}),
          v ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧ v ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = b ∧
          v ≫ mY.1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw.solution
