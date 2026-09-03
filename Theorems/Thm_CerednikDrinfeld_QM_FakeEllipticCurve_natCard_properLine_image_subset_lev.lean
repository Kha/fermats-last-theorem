import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_properLine_image_subset_lev
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f)
    (hP₀ : nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))))
    (hgen : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k))) →
        ∃ m : ↥Λ, P = pushPt (E.act m) (E.act_over m) P₀)
    (hann : ∀ m : ↥Λ, pushPt (E.act m) (E.act_over m) P₀ = E.L.one (𝟙 (Spec (CommRingCat.of k))) ↔
      ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = ((ℓ : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) :
    Nat.card {J : Submodule ℤ ℍ[ℚ, a, b] //
        (J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
          (∃ x ∈ J, ¬ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) ∧ J ≠ Λ) ∧
        ∀ m : ↥Λ, (m : ℍ[ℚ, a, b]) ∈ J → FactorsThrough E.lev (pushPt (E.act m) (E.act_over m) P₀)} =
      (if ℓ ∣ N then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_properLine_image_subset_lev.solution
