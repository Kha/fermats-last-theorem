import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_tateProdRep_quadratic_of_forall

set_option autoImplicit false

open scoped TensorProduct

namespace DrinfeldCurve

theorem tateProdRep_quadratic_of_forall
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (S : Type)
    (θ : (GaloisField q 2)ˣ →* Eˣ) {W : Type*} [AddCommGroup W] [Module E W]
    (σ : Representation E (CuspidalType.GL2 q) W)
    (hT : ∀ u : W →ₗ[E]
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))),
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q),
        u ∘ₗ σ g = tateRep q k ℓ E ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ hSubgroup q),
        let A : (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) →
            (W →ₗ[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) :=
          fun v => tateRep q k ℓ E ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Eˣ) : E) + ((θ (α ^ q) : Eˣ) : E)) • A u +
          (((θ α : Eˣ) : E) * ((θ (α ^ q) : Eˣ) : E)) • u = 0) :
    ∀ u : W →ₗ[E] tateProd q k ℓ E S,
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ hSubgroup q),
        u ∘ₗ σ g = tateProdRep q k ℓ E S ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ hSubgroup q),
        let A : (W →ₗ[E] tateProd q k ℓ E S) → (W →ₗ[E] tateProd q k ℓ E S) :=
          fun v => tateProdRep q k ℓ E S ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Eˣ) : E) + ((θ (α ^ q) : Eˣ) : E)) • A u +
          (((θ α : Eˣ) : E) * ((θ (α ^ q) : Eˣ) : E)) • u = 0 := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_tateProdRep_quadratic_of_forall.solution
