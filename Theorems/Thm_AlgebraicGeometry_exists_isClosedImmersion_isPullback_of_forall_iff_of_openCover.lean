import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover
    {X : Scheme.{u}} {ι : Type u} (U : ι → Scheme.{u}) (g : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    [∀ i, QuasiCompact (g i)]
    (hcover : ∀ x : ↥X, ∃ i, x ∈ Set.range (g i).base)
    (Z : ι → Scheme.{u}) (z : ∀ i, Z i ⟶ U i) [∀ i, IsClosedImmersion (z i)]
    (hagree : ∀ (i j : ι) {T : Scheme.{u}} (Pᵢ : T ⟶ U i) (Pⱼ : T ⟶ U j),
      Pᵢ ≫ g i = Pⱼ ≫ g j → ((∃ Q : T ⟶ Z i, Q ≫ z i = Pᵢ) ↔ (∃ Q : T ⟶ Z j, Q ≫ z j = Pⱼ))) :
    ∃ (K : Scheme.{u}) (k : K ⟶ X), IsClosedImmersion k ∧
      (∀ i, ∃ zK : Z i ⟶ K, IsPullback (z i) zK (g i) k) ∧
      (∀ {T : Scheme.{u}} (P : T ⟶ X), (∃ Q : T ⟶ K, Q ≫ k = P) ↔
        ∀ (i : ι) (V : T.Opens) (PV : (V : Scheme.{u}) ⟶ U i), V.ι ≫ P = PV ≫ g i →
          ∃ Q : (V : Scheme.{u}) ⟶ Z i, Q ≫ z i = PV) ∧
      (∀ (K' : Scheme.{u}) (k' : K' ⟶ X), IsClosedImmersion k' →
        (∀ (i : ι) {T : Scheme.{u}} (P : T ⟶ U i),
          (∃ Q : T ⟶ K', Q ≫ k' = P ≫ g i) ↔ (∃ Q : T ⟶ Z i, Q ≫ z i = P)) →
        ∀ {T : Scheme.{u}} (P : T ⟶ X), (∃ Q : T ⟶ K', Q ≫ k' = P) ↔ (∃ Q : T ⟶ K, Q ≫ k = P)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_forall_iff_of_openCover.solution
