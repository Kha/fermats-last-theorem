import Mathlib
import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (star : ↥Λ → ↥Λ)
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (b0 c : ↥Λ) (hc : (c : ℍ[ℚ, a, b]) = (6 : ℚ) • (1 + (star b0 : ℍ[ℚ, a, b]) * (b0 : ℍ[ℚ, a, b]))) :
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      pushPt (act c) (act_over c) x =
        L.nsmul t (2 * 3) (L.mul t x (pushPt (act (star b0)) (act_over (star b0)) (pushPt (act b0) (act_over b0) x))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_pushPt_act_eq_nsmul_mul_pushPt_act_star_pushPt_act_of_eq_smul_one_add_star_mul.solution
