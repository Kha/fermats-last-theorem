import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_act_add_mul_zsmul_neg_pointCommGroup

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.act_add_mul_zsmul_neg_pointCommGroup
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) :
    letI := L.pointCommGroup hc f
    (∀ x y : ↥Λ, (⟨act (x + y), act_over (x + y)⟩ : SchemeHomOver f f) = ⟨act x, act_over x⟩ * ⟨act y, act_over y⟩) ∧
    (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      (⟨act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩, act_over _⟩ : SchemeHomOver f f) =
        NeronModelInfra.schemeHomOverComp (⟨act y, act_over y⟩ : SchemeHomOver f f) ⟨act x, act_over x⟩) ∧
    (∀ k : ℤ, (⟨act (k • ⟨1, hΛ.isOrder.one_mem⟩), act_over _⟩ : SchemeHomOver f f) =
        (RelativeGroupLaw.idPoint : SchemeHomOver f f) ^ k) ∧
    (∀ x : ↥Λ, (⟨act (-x), act_over (-x)⟩ : SchemeHomOver f f) = (⟨act x, act_over x⟩ : SchemeHomOver f f)⁻¹) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t P Q) (⟨act x, act_over x⟩ : SchemeHomOver f f) =
        L.mul t (NeronModelInfra.schemeHomOverComp P ⟨act x, act_over x⟩)
          (NeronModelInfra.schemeHomOverComp Q ⟨act x, act_over x⟩)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_act_add_mul_zsmul_neg_pointCommGroup.solution
