import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (P₁ P : E.FullLevel m) (ℓ : ℕ) (hℓm : ℓ ∣ m) (K : E.ExtraLevel ℓ)
    (L L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (hL₀ : L₀ ≤ Λ)
    (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L)
    (hLd : ∀ x : ℍ[ℚ, a, b], x ∈ L → x * (d : ℍ[ℚ, a, b]) ∈ L₀)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (hP : FakeEllipticCurve.sectionAt P.P k sk = pushPt (E.act c) (E.act_over c) (FakeEllipticCurve.sectionAt P₁.P k sk))
    (hK : ∀ Q : SchemeHomOver (geomPoint k sk) E.f,
      FactorsThrough K.levK Q ↔
        ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧
          pushPt (E.act x) (E.act_over x)
            (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P₁.P k sk)) = Q)
    (Q : SchemeHomOver (geomPoint k sk) E.f) :
    FactorsThrough K.levK Q ↔
      ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
        pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_iff_of_mul_mem_of_sectionAt_eq.solution
