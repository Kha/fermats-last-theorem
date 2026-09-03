import Definitions.Def_CerednikDrinfeld_MumfordGlue

import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_isProper_zb
attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀
attribute [-simp] CerednikDrinfeld.Mumford.smulHom_apply CerednikDrinfeld.Mumford.smulHom_mapDart CerednikDrinfeld.Mumford.walkCycle_nil

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    ∀ n : ℕ, IsProper (Gl.zb n) := by
  intro n
  obtain ⟨hft, hqc⟩ := CerednikDrinfeld.FormalOmega.MumfordGlue.locallyOfFiniteType_and_quasiCompact 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl n
  haveI := hft
  haveI := hqc
  haveI : IsSeparated (Gl.zb n) := Gl.zb_isSeparated n
  have hex : ValuativeCriterion.Existence (Gl.zb n) := by
    intro S
    obtain ⟨yV, h1, h2⟩ := CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl n
      S.R S.K S.i₁ S.i₂ S.commSq.w.symm
    exact ⟨⟨yV, h1, h2⟩⟩
  haveI : UniversallyClosed (Gl.zb n) := UniversallyClosed.of_valuativeCriterion (Gl.zb n) hex
  exact {}
