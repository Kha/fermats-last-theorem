import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer

set_option autoImplicit false

open IsLocalRing

theorem AlgebraicCurve.NodeRingLayers.isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer
    {L : Type} [Field L] {F : Type} [Field F] [Algebra L F]

    (C' : Subring L) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C') (hϖ'irr : Irreducible ϖ')

    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hϖ'N₀ : ¬ IsUnit (⟨algebraMap L F ((ϖ' : ↥C') : L), hC'N₀ _ ϖ'.2⟩ : ↥N₀))
    (hdim : 2 ≤ ringKrullDim ↥N₀)

    (C'' : Subring L) (hC'C'' : C' ≤ C'') [IsDomain ↥C''] [IsDiscreteValuationRing ↥C''] (ϖ'' : ↥C'') (hϖ''irr : Irreducible ϖ'')
    (e : ℕ) (he : 1 ≤ e) (hϖe : ∃ v : L, v ∈ C'' ∧ v⁻¹ ∈ C'' ∧ ((ϖ' : ↥C') : L) = v * ((ϖ'' : ↥C'') : L) ^ e)
    (R : Subring L) (hC'R : C' ≤ R) (hRC'' : R ≤ C'')
    (hRfin : letI : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra; Module.Finite ↥C' ↥R)
    (hloc : ∀ c : L, c ∈ C'' → ∃ r s : L, r ∈ R ∧ s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ c * s = r)

    (T'' : Subring F) (hT'' : T'' = Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ c : L, c ∈ C'' ∧ f = algebraMap L F c}))
    (𝔐 : Ideal ↥T'')
    (h𝔐 : 𝔐 = Ideal.span ({t : ↥T'' | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T'' | (t : F) = algebraMap L F ((ϖ'' : ↥C'') : L)}))
    :
    𝔐.IsMaximal ∧
    ∃ (TL : Subring F), (∀ f : F, f ∈ TL ↔ ∃ a b : ↥T'', b ∉ 𝔐 ∧ f * (b : F) = (a : F)) ∧
    ∃ (_ : IsNoetherianRing ↥TL) (_ : IsLocalRing ↥TL) (hle : N₀ ≤ TL),

      (∀ f : ↥N₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion hle f)) ∧

      (∀ g : ↥TL, ∃ (o : ↥C'') (h : algebraMap L F (o : L) ∈ TL), ¬ IsUnit (g - ⟨_, h⟩)) ∧

      (∀ hϖ'' : algebraMap L F ((ϖ'' : ↥C'') : L) ∈ TL,
        maximalIdeal ↥TL ≤ (maximalIdeal ↥N₀).map (Subring.inclusion hle) ⊔ Ideal.span {⟨_, hϖ''⟩}) ∧
      2 ≤ ringKrullDim ↥TL := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer.solution
