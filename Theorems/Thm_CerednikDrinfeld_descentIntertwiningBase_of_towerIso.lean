import Definitions.Def_CerednikDrinfeld_DescentIntertwiningBase
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_descentIntertwiningBase_of_towerIso

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.Omega AlgebraicCurve

theorem CerednikDrinfeld.descentIntertwiningBase_of_towerIso

    {q q' : ℕ} (r : ℕ) (ir irbar : Fin 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [Fact (A.DecompositionIsometric ℚ)]
    [DecidableEq A.valuation.Completion]

    {a b : ℚ}
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A)))
    (ϖ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A) A.valuation.Completion)
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Γ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a, b])ˣ)
    (w wbar : HeckeTower.Obj q q' → (ℍ[ℚ, a, b])ˣ)
    (s : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a, b])ˣ)
    (dIso : ↥(A.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A) A.valuation.Completion)

    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀]
    (gal₀ : ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) F₀)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) F₀)
    (χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))

    (𝕋 𝕋' : HeckeTower.TowerData q q' F₀)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (galT' : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋'.F ℓ))
    (WT' : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋'.F ℓ))

    (θ : ∀ ℓ : HeckeTower.AwayPrime q q', 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] 𝕋'.F ℓ)
    (hθ : ∀ (α : HeckeTower.Arr q q') (x : F₀), θ α.1 (𝕋.φ α x) = 𝕋'.φ α x)

    (ιM' : ∀ j : HeckeTower.Obj q q', 𝕋'.objField j →+* FractionRing (Omega.HolRingOf ϖ ρ))
    (ιM : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ ρ))
    (hι₀ : ∀ x : F₀, ιM none x = ιM' none x)
    (hιℓ : ∀ (ℓ : HeckeTower.AwayPrime q q') (x : 𝕋.F ℓ), ιM (some ℓ) x = ιM' (some ℓ) (θ ℓ x))
    (hBase : CerednikDrinfeld.DescentIntertwiningBase r ir irbar A ρ ϖ Γ w wbar s dIso F₀ 𝕋' gal₀ galT' W WT' χ ιM') :
    CerednikDrinfeld.DescentIntertwiningBase r ir irbar A ρ ϖ Γ w wbar s dIso F₀ 𝕋 gal₀ galT W WT χ ιM := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_descentIntertwiningBase_of_towerIso.solution
