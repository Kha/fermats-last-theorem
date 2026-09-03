import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian
    (k F : Type) [Field k] [CharZero k] [Field F] [Algebra k F]
    (L : IntermediateField k F) [Algebra.IsAlgebraic k ↥L]
    (A : ValuationSubring ↥L) (π₀ : k)
    (hπ₀ : π₀ ∈ A.comap (algebraMap k ↥L))
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap k ↥L)))
    (hunif : maximalIdeal ↥(A.comap (algebraMap k ↥L)) = Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap k ↥L)))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap k ↥L)))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap k ↥L)))) :
    (∀ a : ↥L, a ∈ A → IsIntegral ↥(A.comap (algebraMap k ↥L)) a) ∧
    (∀ s : Finset ↥L, ∃ (n : ℕ) (ϖ' : ↥L) (u v : ↥A), 0 < n ∧ ϖ' ∈ A ∧ (u : ↥L) * v = 1 ∧
        (∀ x ∈ s, (x : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) ∧
        Module.finrank k ↥(IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) = n ∧
        ϖ' ^ n = algebraMap k ↥L π₀ * (u : ↥L) ∧
        (∀ a : ↥L, a ∈ A → (a : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)} → a ≠ 0 →
          ∃ (m : ℕ) (w z : ↥A), (w : ↥L) * z = 1 ∧ a = ϖ' ^ m * (w : ↥L))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian.solution
