import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_zb
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_affineNbhd_of_affineNbhd_zero
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_and_affineNbhd
attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N) :
    (∀ n : ℕ, IsProper (Gl.zb n)) ∧
    (∀ (n : ℕ) (S : Set (Gl.Z n)), S.Finite → ∃ U : (Gl.Z n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (Gl.Z n))) := by
  refine ⟨CerednikDrinfeld.FormalOmega.MumfordGlue.isProper_zb 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl, ?_⟩
  exact CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_of_affineNbhd_zero 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl
    (fun S hS => CerednikDrinfeld.FormalOmega.MumfordGlue.affineNbhd_zero 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl S hS)
