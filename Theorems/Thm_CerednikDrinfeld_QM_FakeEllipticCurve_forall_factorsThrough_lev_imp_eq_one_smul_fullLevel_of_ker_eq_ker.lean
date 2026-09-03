import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (p : PrimeSpectrum S)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (sk₀ : S →+* k₀) (hsk₀ : RingHom.ker sk₀ = p.asIdeal)
    (h₀ : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀)) = E.L.one (geomPoint k₀ sk₀))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hsk : RingHom.ker sk = p.asIdeal) :
    ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker.solution
