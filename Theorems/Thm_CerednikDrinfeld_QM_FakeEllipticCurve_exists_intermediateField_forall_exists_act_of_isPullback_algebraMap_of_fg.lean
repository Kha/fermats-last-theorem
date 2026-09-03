import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic~surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve"
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : Λ.FG) {N : ℕ}
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    (E : FakeEllipticCurve Λ N K)
    {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀]
    (g : E.A ⟶ X₀) (hg : CategoryTheory.IsPullback g E.f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K)))) :
    ∃ (Lι : IntermediateField k K) (_ : FiniteDimensional k ↥Lι) (_ : L ≤ Lι),
      ∀ (L'' : IntermediateField k K) (_ : Lι ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ : Scheme.{0}) (f₂ : X₂ ⟶ Spec (CommRingCat.of ↥L''))
        (r : E.A ⟶ X₂) (hr : CategoryTheory.IsPullback r E.f f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (q : X₂ ⟶ X₀) (_ : CategoryTheory.IsPullback q f₂ f₀ (Spec.map (CommRingCat.ofHom j))) (_ : r ≫ q = g)
        (L₂ : RelativeGroupLaw ↥L'' f₂)
        (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t' E.f),
          (E.L.mul t' P Q).1 ≫ r =
            (L₂.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K)))
              ⟨P.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ r, by rw [Category.assoc, hr.w, ← Category.assoc, Q.2]⟩).1),
        ∃ (act₂ : ↥Λ → (X₂ ⟶ X₂)) (hact₂ : ∀ x : ↥Λ, act₂ x ≫ f₂ = f₂),
          (∀ x : ↥Λ, E.act x ≫ r = r ≫ act₂ x) ∧
          (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P Q : SchemeHomOver t f₂),
            pushPt (act₂ x) (hact₂ x) (L₂.mul t P Q) =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ x) (hact₂ x) Q)) ∧
          (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act₂ ⟨1, h⟩ = 𝟙 X₂) ∧
          (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
            act₂ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act₂ y ≫ act₂ x) ∧
          (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥L'')) (P : SchemeHomOver t f₂),
            pushPt (act₂ (x + y)) (hact₂ (x + y)) P =
              L₂.mul t (pushPt (act₂ x) (hact₂ x) P) (pushPt (act₂ y) (hact₂ y) P)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_exists_act_of_isPullback_algebraMap_of_fg.solution
