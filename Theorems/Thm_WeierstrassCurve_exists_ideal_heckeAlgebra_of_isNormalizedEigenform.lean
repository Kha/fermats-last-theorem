import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open CuspForm

theorem WeierstrassCurve.exists_ideal_heckeAlgebra_of_isNormalizedEigenform (p : ℕ) (W : WeierstrassCurve ℤ) {L : ℕ} [NeZero L] (S₀ : Set ℕ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNormalizedEigenform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S₀ →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra L 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra L 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ L),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra L 2 S₀) ∈ 𝔪₂ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_of_isNormalizedEigenform.solution
