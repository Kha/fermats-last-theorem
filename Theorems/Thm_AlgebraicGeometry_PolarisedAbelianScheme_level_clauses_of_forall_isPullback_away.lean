import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_level_clauses_of_forall_isPullback_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.level_clauses_of_forall_isPullback_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (L' : ∀ i, RelativeGroupLaw (B i) (f' i))
    (hLmul : ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (B i))) (x y : SchemeHomOver t' (f' i)),
      ((L' i).mul t' x y).1 ≫ g i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    {g₀ n : ℕ} (P : Fin (2 * g₀) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (P' : ∀ i, Fin (2 * g₀) → SchemeHomOver (𝟙 (Spec (CommRingCat.of (B i)))) (f' i))
    (hP : ∀ (i : Fin k) (j : Fin (2 * g₀)), (P' i j).1 ≫ g i = Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ (P j).1)
    (h : ∀ i : Fin k,
      (∀ j, (L' i).nsmul (𝟙 (Spec (CommRingCat.of (B i)))) n (P' i j) = (L' i).one (𝟙 (Spec (CommRingCat.of (B i))))) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : (B i) →+* K) (c c' : Fin (2 * g₀) → Fin n),
        (L' i).finComb (Spec.map (CommRingCat.ofHom sK))
            (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i j)) (fun j => (c j : ℕ)) =
          (L' i).finComb (Spec.map (CommRingCat.ofHom sK))
            (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i j)) (fun j => (c' j : ℕ)) →
          c = c') ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : (B i) →+* K) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sK)) (f' i)),
        (L' i).nsmul (Spec.map (CommRingCat.ofHom sK)) n Q = (L' i).one (Spec.map (CommRingCat.ofHom sK)) →
          ∃ c : Fin (2 * g₀) → Fin n,
            (L' i).finComb (Spec.map (CommRingCat.ofHom sK))
              (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P' i j)) (fun j => (c j : ℕ)) = Q)) :
    (∀ j, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P j) = L.one (𝟙 (Spec (CommRingCat.of S)))) ∧
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S →+* K) (c c' : Fin (2 * g₀) → Fin n),
      L.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P j)) (fun j => (c j : ℕ)) =
        L.finComb (Spec.map (CommRingCat.ofHom sK))
          (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P j)) (fun j => (c' j : ℕ)) →
        c = c') ∧
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (sK : S →+* K) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sK)) f),
      L.nsmul (Spec.map (CommRingCat.ofHom sK)) n Q = L.one (Spec.map (CommRingCat.ofHom sK)) →
        ∃ c : Fin (2 * g₀) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sK))
            (fun j => schemeHomOverComp (Spec.map (CommRingCat.ofHom sK)) (Category.comp_id _) (P j)) (fun j => (c j : ℕ)) = Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_level_clauses_of_forall_isPullback_away.solution
