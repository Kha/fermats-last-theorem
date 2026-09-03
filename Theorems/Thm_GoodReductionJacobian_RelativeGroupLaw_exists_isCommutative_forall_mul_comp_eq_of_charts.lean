import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_forall_mul_comp_eq_of_charts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_forall_mul_comp_eq_of_charts
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hsurj : ∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(A' i)), (ι i).base x = y)
    (L' : ∀ i, RelativeGroupLaw (B i) (f' i)) (hcomm : ∀ i, (L' i).IsCommutative)
    (hagree : ∀ (i j : Fin k) {T : Scheme.{u}} (tᵢ : T ⟶ Spec (CommRingCat.of (B i))) (tⱼ : T ⟶ Spec (CommRingCat.of (B j)))
        (a b : SchemeHomOver tᵢ (f' i)) (a' b' : SchemeHomOver tⱼ (f' j)),
        a.1 ≫ ι i = a'.1 ≫ ι j → b.1 ≫ ι i = b'.1 ≫ ι j →
          ((L' i).mul tᵢ a b).1 ≫ ι i = ((L' j).mul tⱼ a' b').1 ≫ ι j) :
    ∃ L : RelativeGroupLaw S f, L.IsCommutative ∧
      ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (B i))) (x y : SchemeHomOver t' (f' i)),
        ((L' i).mul t' x y).1 ≫ ι i =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
            ⟨x.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, y.2]⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_forall_mul_comp_eq_of_charts.solution
