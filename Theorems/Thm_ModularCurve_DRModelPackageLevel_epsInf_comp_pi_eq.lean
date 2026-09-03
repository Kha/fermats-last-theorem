import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem epsInf_comp_pi_eq (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (φinf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hφinf : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ q),
      ((φinf x : DRLevel.R q) : ℚ) = ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase0 N₀ q))
    (hε₀ : ε₀.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ q) :
    𝔓.εinf.1 ≫ 𝔓.π.1 = ε₀.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq.solution

end ModularCurve.DRModelPackageLevel
