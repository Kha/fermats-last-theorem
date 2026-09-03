import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart
attribute [-instance] instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicGeometry.forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart

    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (ηi ηj x : X) (hij : ηi ≠ ηj) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hxns : x ∉ toBase.smoothLocus) (hi : ηi ⤳ x) (hj : ηj ⤳ x)
    (hηi : toBase.base ηi = closedPoint ↥A) (hηj : toBase.base ηj = closedPoint ↥A)
    (hηi' : ∃ y : X, ηi ⤳ y ∧ y ≠ ηi) (hηj' : ∃ y : X, ηj ⤳ y ∧ y ≠ ηj)
    (honly : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = ηi ∨ η = ηj)

    (hval : ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)

    (huniq : ∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') → ηi ⤳ x' → ηj ⤳ x' → x' = x)

    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)
    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hNi : N₀ ≤ SemistableModel.localRing X φ ηi) (hNj : N₀ ≤ SemistableModel.localRing X φ ηj)

    (xN yN uN : F) (hxN : xN ∈ N₀) (hyN : yN ∈ N₀) (huN : ∃ hu : uN ∈ N₀, IsUnit (⟨uN, hu⟩ : ↥N₀))
    (ϖ₀ : L) (hϖ₀C : ϖ₀ ∈ C') (hϖ₀ : ϖ₀ ≠ 0) (E₀ : ℕ)
    (hxy : xN * yN = algebraMap L F ϖ₀ ^ E₀ * uN)
    (hmod : ∃ h : ϖ₀ ^ E₀ ∈ A, (⟨ϖ₀ ^ E₀, h⟩ : ↥A) ∈ maximalIdeal ↥A)
    (hx_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, xN * g = 1)
    (hx_u : ∃ g ∈ SemistableModel.localRing X φ ηj, xN * g = 1)
    (hy_nu : ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, yN * g = 1)
    (hy_u : ∃ g ∈ SemistableModel.localRing X φ ηi, yN * g = 1)

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

    (Bx : Subring F) (hBxN₀ : ∀ f : F, f ∈ Bx → f ∈ N₀)
    (hxB : xN ∈ Bx) (hyB : yN ∈ Bx) (huB : uN ∈ Bx)
    (hN₀Bx : ∀ f : F, f ∈ N₀ ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ N₀, IsUnit (⟨h, hh⟩ : ↥N₀)) ∧ f * h = g)
    (hBxfg : ∃ T : Finset F, Bx = Subring.closure
      ({f : F | ∃ c : L, c ∈ C' ∧ f = algebraMap L F c} ∪ (↑T : Set F)))

    (hcent : ∀ η : X, toBase.base η = closedPoint ↥A → (∃ y : X, η ⤳ y ∧ y ≠ η) →
      Bx ≤ SemistableModel.localRing X φ η →
        ∃ f ∈ Bx, (∀ hf : f ∈ N₀, ¬ IsUnit (⟨f, hf⟩ : ↥N₀)) ∧ ∃ g ∈ SemistableModel.localRing X φ η, f * g = 1)
    :
    ∀ 𝔮 : Ideal ↥T, 𝔮.IsPrime →
      (∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ T), a ∈ maximalIdeal ↥A →
        (⟨algebraMap L F (a : L), h⟩ : ↥T) ∈ 𝔮) →
      𝔮 ≤ 𝔭 → 𝔮 ≠ 𝔭 →
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηi, (t : F) * g = 1) ∨
      (∀ t : ↥T, t ∈ 𝔮 ↔ ¬ ∃ g ∈ SemistableModel.localRing X φ ηj, (t : F) * g = 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_forall_mem_iff_not_exists_or_of_isPrime_of_ne_nodeIdeal_of_nodeChart.solution
