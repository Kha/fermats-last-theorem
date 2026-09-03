import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_prod_zpow_baseChange_and_isHomOnPoints

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) (e : Fin n → ℤ) :
    (∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
      (letI := L.pointCommGroup hc (pullback.snd f s'' ≫ s'');
          (∏ l, (⟨pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]⟩ : SchemeHomOver (pullback.snd f s'' ≫ s'') f) ^ (e l))).1 =
        pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫
          (letI := L.pointCommGroup hc (pullback.snd f s ≫ s);
          (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (e l))).1) ∧
    (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : Fin n → (pullback f s ⟶ A)) (hφ : ∀ l, φ l ≫ f = pullback.snd f s ≫ s),
      (∀ l, (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ l =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ φ l, by rw [Category.assoc, hφ l, ← Category.assoc, pullback.lift_snd]⟩).1)) →
      ∀ (ω : pullback f s ⟶ A) (hω : ω ≫ f = pullback.snd f s ≫ s),
        ω = (letI := L.pointCommGroup hc (pullback.snd f s ≫ s);
          (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (e l))).1 →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ ω =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩).1)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_prod_zpow_baseChange_and_isHomOnPoints.solution
