import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.RelativeGroupLaw.setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    {S' : Type} [CommRing S'] (φ : S →+* S')
    {A' : Scheme} {f' : A' ⟶ Spec (CommRingCat.of S')} (L' : RelativeGroupLaw S' f')
    (gA : A' ⟶ A) (hgA : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hgA_mul : ∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ gA =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hgA.w, ← Category.assoc, y.2]⟩).1)
    (P' : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S'))) f')
    (hP' : ∀ i, (P' i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (P i).1) :
    {s : ↥(Spec (CommRingCat.of S')) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k),
      RingHom.ker sk = s.asIdeal →
      (∀ c c' : Fin (2 * g) → Fin n,
        L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c i : ℕ)) =
          L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c' i : ℕ)) →
        c = c') ∧
      (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f',
        L'.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L'.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L'.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P' i)) (fun i => (c i : ℕ)) = Q)} =
      (Spec.map (CommRingCat.ofHom φ)).base ⁻¹' {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
        RingHom.ker sk = s.asIdeal →
        (∀ c c' : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
          c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin (2 * g) → Fin n,
            L.finComb (Spec.map (CommRingCat.ofHom sk))
              (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q)} := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_setOf_finComb_injective_and_forall_torsion_exists_baseChange_eq_preimage.solution
