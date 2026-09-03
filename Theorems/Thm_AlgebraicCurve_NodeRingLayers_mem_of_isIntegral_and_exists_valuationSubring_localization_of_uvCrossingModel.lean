import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeRingLayers_mem_of_isIntegral_and_exists_valuationSubring_localization_of_uvCrossingModel
attribute [-instance] instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeRingLayers.mem_of_isIntegral_and_exists_valuationSubring_localization_of_uvCrossingModel
    {L : Type} [Field L] [CharZero L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]

    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (hϖ'irr : Irreducible ϖ')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)

    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hdim : 2 ≤ ringKrullDim ↥N₀)

    (Wc : Type) [CommRing Wc] [IsDomain Wc] [IsDiscreteValuationRing Wc] [IsAdicComplete (maximalIdeal Wc) Wc]
    (πW : Wc) (hirr : Irreducible πW) (E : ℕ) (hE : 1 ≤ E)
    (σ : Wc →+* AdicCompletion (maximalIdeal ↥N₀) ↥N₀)
    (ιc : AdicCompletion (maximalIdeal ↥N₀) ↥N₀ ≃+* UVCrossingModel Wc (πW ^ E))
    (hσπ : ∀ h : algebraMap L F ((ϖ' : ↥C') : L) ∈ N₀,
      σ πW = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)
    (hισ : ∀ o : Wc, ιc (σ o) = const (πW ^ E) o)
    (hσC : ∀ (c : ↥C') (h : algebraMap L F (c : L) ∈ N₀),
      ∃ o : Wc, σ o = algebraMap ↥N₀ (AdicCompletion (maximalIdeal ↥N₀) ↥N₀) ⟨_, h⟩)

    (T : Subring F) (hT : T = Subring.closure ((N₀ : Set F) ∪ Set.range (fun a : ↥A => algebraMap L F (a : L))))
    (hfrac : ∀ f : F, ∃ b c : ↥T, (c : F) ≠ 0 ∧ f * (c : F) = (b : F))
    (𝔭 : Ideal ↥T)
    (h𝔭 : 𝔭 = Ideal.span ({t : ↥T | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T | ∃ a : ↥A, a ∈ maximalIdeal ↥A ∧ (t : F) = algebraMap L F (a : L)}))

    (Lx : Subring F) (hLx : ∀ f : F, f ∈ Lx ↔ ∃ b c : ↥T, c ∉ 𝔭 ∧ f * (c : F) = (b : F)) :
    (∀ f : F, IsIntegral ↥Lx f → f ∈ Lx) ∧
    (∀ Q : Ideal ↥Lx, Q.IsPrime →
      (∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ Lx), a ∈ maximalIdeal ↥A → (⟨_, h⟩ : ↥Lx) ∈ Q) →
      (∃ g : ↥Lx, g ∉ Q ∧ ¬ IsUnit g) →
      ∃ W : ValuationSubring F, ∀ f : F, f ∈ W ↔ ∃ b c : ↥Lx, c ∉ Q ∧ f * (c : F) = (b : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeRingLayers_mem_of_isIntegral_and_exists_valuationSubring_localization_of_uvCrossingModel.solution
