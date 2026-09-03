import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_weight_eq

open scoped Classical in
theorem FrobeniusDensity.weight_eq {G : Type*} [Group G] [Finite G] (σ τ : G) :
    ∑ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
          ((f : ℤ) * ({x : G ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) | τ • x = x}.ncard : ℤ))
      = ({g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_weight_eq.solution
