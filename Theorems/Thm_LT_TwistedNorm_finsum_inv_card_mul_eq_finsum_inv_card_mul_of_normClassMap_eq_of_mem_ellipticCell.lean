import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell

set_option autoImplicit false

theorem LT.TwistedNorm.finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K)
    (RL : Set (GL (Fin 2) L))
    (hRL₁ : ∀ δ₁ ∈ RL, ∀ δ₂ ∈ RL, ∀ (h : GL (Fin 2) L) (u : Lˣ),
      δ₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * δ₁ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) → δ₁ = δ₂)
    (hRL₂ : ∀ (δ : GL (Fin 2) L) (a : Kˣ),
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) →
      ∃ δ₀ ∈ RL, ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h))
    (A : GL (Fin 2) L → Kˣ)
    (hA : ∀ δ₀ ∈ RL, (∃ a : Kˣ,
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₀) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₀) =
        ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) (A δ₀) * γ₀))
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b)
    (Φ : Kˣ → ℂ)
    (hΦS : ∀ a s : Kˣ, (∃ h : GL (Fin 2) K,
        Matrix.GeneralLinearGroup.scalar (Fin 2) s * γ₀ = h⁻¹ * γ₀ * h) → Φ (a * s) = Φ a)
    (hΦN : ∀ (a : Kˣ) (b : Lˣ), Φ (a * Units.map (Algebra.norm K : L →* K) b) = Φ a)
    (hΦ0 : ∀ a : Kˣ, ¬ LT.TwistedNorm.IsNormClass hgen
        (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) → Φ a = 0) :
    (∑ᶠ δ₀ ∈ RL ∩ {δ | ∃ a : Kˣ,
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
          ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)},
      ((Nat.card {q : Lˣ ⧸ (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ).range //
          ∃ u : Lˣ, QuotientGroup.mk u = q ∧ ∃ h : GL (Fin 2) L,
            Matrix.GeneralLinearGroup.scalar (Fin 2) u * δ₀ =
              h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h} : ℕ) : ℂ)⁻¹ * Φ (A δ₀)) =
      ∑ᶠ t ∈ T,
        ((Nat.card {a : Kˣ // ∃ h : GL (Fin 2) K,
            Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ * Φ t := by p2m_exact_reverting @_root_.P2MW.S_LT_TwistedNorm_finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell.solution
