import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.eq_of_constantsTower_of_forall_mem_iff
    (k F : Type) [Field k] [CharZero k] [Field F] [Algebra k F]
    (L F₀ : IntermediateField k F) (hgen : L ⊔ F₀ = ⊤)
    (A : ValuationSubring ↥L) (W₀ : ValuationSubring ↥F₀)
    (hagree : ∀ x : k, algebraMap k ↥L x ∈ A ↔ algebraMap k ↥F₀ x ∈ W₀)
    (hdvr : IsDiscreteValuationRing ↥W₀)
    (π₀ : k) (hπ₀ : algebraMap k ↥F₀ π₀ ∈ W₀)
    (hunif : maximalIdeal ↥W₀ = Ideal.span {(⟨algebraMap k ↥F₀ π₀, hπ₀⟩ : ↥W₀)})

    (hint : ∀ a : ↥L, a ∈ A → IsIntegral ↥(A.comap (algebraMap k ↥L)) a)

    (htower : ∀ s : Finset ↥L, ∃ (n : ℕ) (ϖ' : ↥L) (u v : ↥A), 0 < n ∧ ϖ' ∈ A ∧ (u : ↥L) * v = 1 ∧
        (∀ x ∈ s, (x : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) ∧
        Module.finrank k ↥(IntermediateField.adjoin k {((ϖ' : ↥L) : F)}) = n ∧
        ϖ' ^ n = algebraMap k ↥L π₀ * (u : ↥L) ∧
        (∀ a : ↥L, a ∈ A → (a : F) ∈ IntermediateField.adjoin k {((ϖ' : ↥L) : F)} → a ≠ 0 →
          ∃ (m : ℕ) (w z : ↥A), (w : ↥L) * z = 1 ∧ a = ϖ' ^ m * (w : ↥L)))
    (W W' : ValuationSubring F)
    (hW : ∀ f : ↥F₀, (f : F) ∈ W ↔ f ∈ W₀) (hW' : ∀ f : ↥F₀, (f : F) ∈ W' ↔ f ∈ W₀) :
    W = W' := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff.solution
