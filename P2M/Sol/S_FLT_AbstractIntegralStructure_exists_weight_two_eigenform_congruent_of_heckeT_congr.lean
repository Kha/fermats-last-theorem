import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two
import Theorems.Thm_CuspForm_exists_reductionModule_of_isLatticeRealized
import Theorems.Thm_CuspForm_exists_isMaximal_three_mem_heckeT_sub_mem
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_congruent_of_isMaximal
import P2M.Util
namespace P2MW.S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_heckeT_congr
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

open CuspForm CongruenceSubgroup ModularFormClass EisensteinWeightOne

theorem solution
    {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ}
    (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' := by
  have hN : CuspForm.HasIntegralStructure N 2 :=
    (CuspForm.hasIntegralBasis_iff_hasIntegralStructure_two N).mp h
  obtain ⟨M, hACG, hMod, red, hker, hker', h3M, hop⟩ :=
    CuspForm.exists_reductionModule_of_isLatticeRealized hN h1 hreal
  obtain ⟨𝔪₁, h𝔪₁, h3𝔪₁, hT𝔪₁⟩ :=
    @CuspForm.exists_isMaximal_three_mem_heckeT_sub_mem N _ a h1 hT M hACG hMod
      red hker hker' h3M hop
  obtain ⟨f, hf, 𝔪', h𝔪', h3𝔪', hcong⟩ :=
    CuspForm.exists_isNormalizedEigenform_congruent_of_isMaximal hN 𝔪₁ h𝔪₁ (p := 3) h3𝔪₁
  exact ⟨f, hf, 𝔪', h𝔪', h3𝔪', fun ℓ hℓ hℓN => hcong ℓ hℓ hℓN (a ℓ) (hT𝔪₁ ℓ hℓ hℓN)⟩
