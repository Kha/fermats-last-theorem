import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_act_laws_of_forall_comp_eq_of_forall_away

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.act_laws_of_forall_comp_eq_of_forall_away
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    {d m : ℕ} {S : Type} [CommRing S] (X : PolarisedAbelianScheme 2 d m S)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (Xl : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl : ∀ i, QMStructure Λ star β (Xl i))
    (g : ∀ i, (Xl i).A ⟶ X.A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (Xl i).f X.f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (hgmul : ∀ (i : Fin k) {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
      (x y : SchemeHomOver t' (Xl i).f),
      ((Xl i).L.mul t' x y).1 ≫ g i =
        (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))))
          ⟨x.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (X.A ⟶ X.A)) (act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f)
    (hact : ∀ (i : Fin k) (x : ↥Λ), (tl i).act x ≫ g i = g i ≫ act x) :
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
        pushPt (act x) (act_over x) (X.L.mul t P Q) =
          X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
        pushPt (act (x + y)) (act_over (x + y)) P =
          X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) ∧
      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : S →+* k')
        (V : Type) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) X.f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k' sk) X.f, P ∈ Set.range τ ↔ IsTangentVector X.L k' sk P) →
        (∀ v w : V, τ (v + w) = X.L.mul (tangentBase k' sk) (τ v) (τ w)) →
        (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k' V Φ = (n : k')) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_act_laws_of_forall_comp_eq_of_forall_away.solution
