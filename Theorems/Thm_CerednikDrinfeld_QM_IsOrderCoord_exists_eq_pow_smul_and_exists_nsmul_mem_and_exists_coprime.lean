import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) :
    (∀ (K : ℕ) (m : ↥Λ), (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
        (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m') ∧
      (∀ h : ℍ[ℚ, a, b], ∃ d : ℕ, 0 < d ∧ (d : ℚ) • h ∈ Λ) ∧
      (∀ m m' : ↥Λ, ∃ n : ℕ, n.Coprime q ∧ (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) ∈ Λ) ∧
      (∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime.solution
