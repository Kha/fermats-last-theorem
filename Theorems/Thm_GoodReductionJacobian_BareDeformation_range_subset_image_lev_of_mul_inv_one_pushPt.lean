import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Quaternion TensorProduct NumberField

universe u

theorem GoodReductionJacobian.BareDeformation.range_subset_image_lev_of_mul_inv_one_pushPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (φ₀ : ι → (E₀.A ⟶ E₀.A)) (hφ₀ : ∀ i, φ₀ i ≫ E₀.f = E₀.f) (hφg : ∀ i, φ₀ i ≫ D.g = D.g ≫ φ i)
    (hφ₀_stable : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P → FactorsThrough E₀.lev (pushPt (φ₀ i) (hφ₀ i) P)) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base → Set.range Q.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (D.L.mul t P Q).1.base ⊆ D.g.base '' Set.range E₀.lev.base ∧
            Set.range (D.L.inv t P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)),
        Set.range (D.L.one t).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (pushPt (φ i) (hφ i) P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt.solution
