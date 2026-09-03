import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.NodeAnnulusEngine.exists_localizedBaseChange_of_layer_pos_localization
    {k : Type*} [Field k] [CharZero k]
    {L : Type*} [Field L] [Algebra k L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F)) (hrat : ∀ P ∈ S, P.IsRational) (hSne : S.Nonempty)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (K₀ K' : IntermediateField k L) [FiniteDimensional k ↥K₀] [FiniteDimensional k ↥K'] (hK : K₀ ≤ K')
    (C : Subring L) (hCK₀ : ∀ c : L, c ∈ C ↔ c ∈ A ∧ c ∈ K₀) (hC : ∀ c : L, c ∈ C → c ∈ A)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (C' : Subring L) (hC'K' : ∀ c : L, c ∈ C' ↔ c ∈ A ∧ c ∈ K') (hC' : ∀ c : L, c ∈ C' → c ∈ A)
    [IsDomain ↥C'] [IsDiscreteValuationRing ↥C']
    (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue A ⟨(d : L), hC' d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')

    (𝒩₀ : Subring F) (h𝒩₀ : 𝒩₀ ≤ 𝒩) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)

    (hres : ∀ g : ↥𝒩₀, ∃ (o : ↥C) (h : algebraMap L F (o : L) ∈ 𝒩₀), ¬ IsUnit (g - ⟨_, h⟩))

    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)

    (hreg₁ : ∀ (f : ↥𝒩₀) (h₁ : (f : F) ∈ R₁.integers), 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩) ∧
      (¬ IsUnit f → R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h₁⟩)))
    (hreg₂ : ∀ (f : ↥𝒩₀) (h₂ : (f : F) ∈ R₂.integers), 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩) ∧
      (¬ IsUnit f → R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 < x₂.ord (R₂.residue ⟨f, h₂⟩)))

    (x y : F) (hx : x ∈ 𝒩₀) (hy : y ∈ 𝒩₀)
    (x_fst : ∀ h₁ : x ∈ R₁.integers, R₁.residue ⟨x, h₁⟩ = 0)
    (x_snd : ∀ h₂ : x ∈ R₂.integers, R₂.residue ⟨x, h₂⟩ ≠ 0)
    (y_snd : ∀ h₂ : y ∈ R₂.integers, R₂.residue ⟨y, h₂⟩ = 0)
    (y_fst : ∀ h₁ : y ∈ R₁.integers, R₁.residue ⟨y, h₁⟩ ≠ 0) :
    ∃ (𝒩₀' : Subring F) (_ : IsLocalRing ↥𝒩₀') (_ : IsNoetherianRing ↥𝒩₀') (h01 : 𝒩₀ ≤ 𝒩₀'),
      𝒩₀' ≤ 𝒩 ∧

      (∀ P : Place L F, P ∈ S ↔
        (∀ f : F, f ∈ 𝒩₀' → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥𝒩₀', ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧

      (∀ c : L, c ∈ C' → algebraMap L F c ∈ 𝒩₀') ∧
      (∀ g : ↥𝒩₀', ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ 𝒩₀'), ¬ IsUnit (g - ⟨_, h⟩)) ∧

      (∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀'), LinearIndependent ↥C' c →
        ∑ i, c i • ((a i : ↥𝒩₀') : F) = 0 → ∀ i, a i = 0) ∧

      (∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f)) ∧
      (∀ hϖ : algebraMap L F (ϖ' : L) ∈ 𝒩₀',
        maximalIdeal ↥𝒩₀' ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨_, hϖ⟩}) ∧

      (∀ (f : ↥𝒩₀') (h₁ : (f : F) ∈ R₁.integers), 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩) ∧
        (¬ IsUnit f → R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 < x₁.ord (R₁.residue ⟨f, h₁⟩))) ∧
      (∀ (f : ↥𝒩₀') (h₂ : (f : F) ∈ R₂.integers), 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩) ∧
        (¬ IsUnit f → R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 < x₂.ord (R₂.residue ⟨f, h₂⟩))) ∧

      2 ≤ ringKrullDim ↥𝒩₀' ∧

      (∀ B₀ : Subring F, B₀ ≤ 𝒩₀ →
        (∀ f : F, f ∈ 𝒩₀ ↔ ∃ g h : F, g ∈ B₀ ∧ h ∈ B₀ ∧ (∀ hh : h ∈ 𝒩₀, IsUnit (⟨h, hh⟩ : ↥𝒩₀)) ∧ f * h = g) →
        ∀ f : F, f ∈ 𝒩₀' ↔ ∃ g h : F,
          g ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
          h ∈ Subring.closure ((B₀ : Set F) ∪ {x : F | ∃ c : L, c ∈ C' ∧ x = algebraMap L F c}) ∧
          (∀ hh : h ∈ 𝒩₀', IsUnit (⟨h, hh⟩ : ↥𝒩₀')) ∧ f * h = g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization.solution
