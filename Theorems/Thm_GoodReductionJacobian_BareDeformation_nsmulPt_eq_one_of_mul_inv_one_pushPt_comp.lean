import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_nsmulPt_eq_one_of_mul_inv_one_pushPt_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.BareDeformation.nsmulPt_eq_one_of_mul_inv_one_pushPt_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (hφ_hom : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      pushPt (φ i) (hφ i) (D.L.mul t P Q) = D.L.mul t (pushPt (φ i) (hφ i) P) (pushPt (φ i) (hφ i) Q)) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        nsmulPt D.L t N P = D.L.one t → nsmulPt D.L t N Q = D.L.one t →
          nsmulPt D.L t N (D.L.mul t P Q) = D.L.one t ∧ nsmulPt D.L t N (D.L.inv t P) = D.L.one t) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)), nsmulPt D.L t N (D.L.one t) = D.L.one t) ∧
    (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        nsmulPt D.L t N P = D.L.one t → nsmulPt D.L t N (pushPt (φ i) (hφ i) P) = D.L.one t) ∧
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough E₀.lev P →
          nsmulPt D.L (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) N
              ⟨P.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, P.2]⟩
            = D.L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_nsmulPt_eq_one_of_mul_inv_one_pushPt_comp.solution
