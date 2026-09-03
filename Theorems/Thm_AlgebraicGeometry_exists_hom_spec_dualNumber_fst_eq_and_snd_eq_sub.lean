import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hQ : Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q) :
    ∃ D : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      D ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ D =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P ∧
      (∀ (U : X.Opens) (hPU : ⊤ ≤ P ⁻¹ᵁ U) (hQU : ⊤ ≤ Q ⁻¹ᵁ U) (hDU : ⊤ ≤ D ⁻¹ᵁ U) (g : Γ(X, U)),
        TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U ⊤ hDU).hom g)) =
          TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE U ⊤ hPU).hom g)) ∧
        TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE U ⊤ hDU).hom g)) =
          TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE U ⊤ hPU).hom g)) -
          TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((Q.appLE U ⊤ hQU).hom g))) ∧
      (D = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ D) ↔ P = Q) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub.solution
