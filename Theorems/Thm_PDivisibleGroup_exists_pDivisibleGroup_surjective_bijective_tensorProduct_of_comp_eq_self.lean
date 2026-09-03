import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O (AlgebraicClosure ℚ)]
    {h : ℕ} (H : PDivisibleGroup O p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[O] H.level v).comp (ε' v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[O] H.level v).comp (ε v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[O] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[O] H.level v) =
      WithConv.toConv (AlgHom.id O (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v))
    (h₁ h₂ : ℕ) (hh : h₁ + h₂ = h)
    (hcard₁ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₁))
    (hcard₂ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε' v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₂)) :
    ∃ (H₁ : PDivisibleGroup O p h₁) (H₂ : PDivisibleGroup O p h₂)
      (π₁ : ∀ v, H.level v →ₐc[O] H₁.level v) (π₂ : ∀ v, H.level v →ₐc[O] H₂.level v)
      (σ₁ : ∀ v, H₁.level v →ₐ[O] H.level v) (σ₂ : ∀ v, H₂.level v →ₐ[O] H.level v)
      (Θ : ∀ v, H.level v →ₐc[O] H₁.level v ⊗[O] H₂.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧ (∀ v, Function.Surjective (π₂ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, (π₂ v).comp (H.transition v) = (H₂.transition v).comp (π₂ (v + 1))) ∧
      (∀ v, (π₁ v : H.level v →ₐ[O] H₁.level v).comp (σ₁ v) = AlgHom.id O (H₁.level v)) ∧
      (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[O] H₁.level v) = (ε v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, (π₂ v : H.level v →ₐ[O] H₂.level v).comp (σ₂ v) = AlgHom.id O (H₂.level v)) ∧
      (∀ v, (σ₂ v).comp (π₂ v : H.level v →ₐ[O] H₂.level v) = (ε' v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[O] H₁.level v)
        (π₂ v : H.level v →ₐ[O] H₂.level v) (Coalgebra.comul (R := O) b)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.solution
