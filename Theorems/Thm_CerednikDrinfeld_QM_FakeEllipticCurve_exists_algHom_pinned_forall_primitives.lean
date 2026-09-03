import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_algHom_pinned_forall_primitives

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_algHom_pinned_forall_primitives
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {N : ℕ} {p : ℕ} [Fact p.Prime]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (E : FakeEllipticCurve Λ N k)

    (H : Type) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] [Coalgebra.IsCocomm k H]
    (hH : Module.finrank k H = p ^ (2 * 2))
    (hHp : PDivisibleGroup.Hopf.nsmulAlgHom k H p = (Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H))
    (e : ∀ (T : Type) [CommRing T] [Algebra k T],
      WithConv (H →ₐ[k] T) ≃ E.L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k T))) p)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ E.f) = E.L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
        (g' : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ E.f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1) :
    ∃ Φ : ↥Λ → (H →ₐ[k] H),
      (∀ x : ↥Λ, ∀ (T : Type) [CommRing T] [Algebra k T] (q : WithConv (H →ₐ[k] T)),
          ((e T (.toConv (q.ofConv.comp (Φ x)))).val : SchemeHomOver _ E.f).1 = (e T q).val.1 ≫ E.act x) ∧
      (∀ (x : ↥Λ) (ψ : H →ₐ[k] H), (∀ (T : Type) [CommRing T] [Algebra k T] (q : WithConv (H →ₐ[k] T)),
          ((e T (.toConv (q.ofConv.comp ψ))).val : SchemeHomOver _ E.f).1 = (e T q).val.1 ≫ E.act x) → ψ = Φ x) ∧
      (∀ x : ↥Λ, ∀ v ∈ primitives k H, Φ x v ∈ primitives k H) ∧
      (∀ x y : ↥Λ, ∀ v ∈ primitives k H, Φ (x + y) v = Φ x v + Φ y v) ∧
      (∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Φ ⟨1, h1⟩ = AlgHom.id k H) ∧
      (∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        Φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = (Φ y).comp (Φ x)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_algHom_pinned_forall_primitives.solution
