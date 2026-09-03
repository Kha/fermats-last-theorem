import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd
    (L : Type) [Field L] [NumberField L]
    (N₁ N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (hw₁ : ¬ w.asIdeal ∣ N₁) (hw : ¬ w.asIdeal ∣ N)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v)
    (hvU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ levelOne (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L,
      v (g * u) = v g)
    (a : ℂ)
    (ha : SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w v a) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (rightConv L v φ) a := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd.solution
