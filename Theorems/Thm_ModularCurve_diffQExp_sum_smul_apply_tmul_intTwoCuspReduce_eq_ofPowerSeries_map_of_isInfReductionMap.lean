import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (K : Type*) [Field K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    {n : ℕ} (a : Fin n → ↥(integralClosure ℤ ℂ)) (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ i, f i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pg : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ℂ)) • f i))) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (∑ i, φ (a i) • ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hf i)⟩)) =
      HahnSeries.ofPowerSeries ℤ K (pg.map φ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap.solution
