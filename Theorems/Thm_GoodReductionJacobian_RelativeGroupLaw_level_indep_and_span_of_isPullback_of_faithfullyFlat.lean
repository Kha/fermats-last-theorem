import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.level_indep_and_span_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {m : ℕ} (n : ℕ) (P : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (P' : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f')
    (hP : ∀ i, (P' i).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ (P i).1)
    (hindep' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (c₁ c₂ : Fin m → Fin n),
      L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₁ i : ℕ)) =
        L'.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂)
    (hspan' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S' →+* K) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sK)) f'),
      L'.nsmul (Spec.map (CommRingCat.ofHom sK)) n Q = L'.one (Spec.map (CommRingCat.ofHom sK)) →
        ∃ e : Fin m → Fin n,
          L'.finComb (Spec.map (CommRingCat.ofHom sK))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i)) (fun i => (e i : ℕ)) = Q) :
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c₁ c₂ : Fin m → Fin n),
      L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₁ i : ℕ)) =
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c₂ i : ℕ)) →
        c₁ = c₂) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
      L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ e : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (e i : ℕ)) = Q) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat.solution
