import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_localization_atPrime_tensor_of_isAlgClosed
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem IsRegularLocalRing.localization_atPrime_tensor_of_isAlgClosed
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] (R : Type u) [CommRing R] [Algebra k₀ R]
    [Algebra.FiniteType k₀ R] (n : ℕ)
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p) ∧
        ringKrullDim (Localization.AtPrime p) = (n : ℕ∞))
    (k : Type u) [Field k] [Algebra k₀ k] (q : Ideal (k ⊗[k₀] R)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_localization_atPrime_tensor_of_isAlgClosed.solution
