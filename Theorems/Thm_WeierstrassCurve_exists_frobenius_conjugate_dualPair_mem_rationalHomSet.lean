import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve

theorem WeierstrassCurve.exists_frobenius_conjugate_dualPair_mem_rationalHomSet
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W W' : WeierstrassCurve κ) [W.IsElliptic] [W'.IsElliptic]
    (ψ : W.toAffine.Point →+ W'.toAffine.Point) (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (ψ' : W'.toAffine.Point →+ W.toAffine.Point) (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (N : ℕ) (h₁ : ψ'.comp ψ = (N : ℕ) • AddMonoidHom.id _) (h₂ : ψ.comp ψ' = (N : ℕ) • AddMonoidHom.id _) :
    WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W) ∈
        WeierstrassCurve.rationalHomSet κ W (W.map (frobenius κ p)) ∧
    WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W') ∈
        WeierstrassCurve.rationalHomSet κ W' (W'.map (frobenius κ p)) ∧
    ∃ (ψF : (W.map (frobenius κ p)).toAffine.Point →+ (W'.map (frobenius κ p)).toAffine.Point)
      (ψF' : (W'.map (frobenius κ p)).toAffine.Point →+ (W.map (frobenius κ p)).toAffine.Point),
      ψF ∈ WeierstrassCurve.rationalHomSet κ (W.map (frobenius κ p)) (W'.map (frobenius κ p)) ∧
      ψF' ∈ WeierstrassCurve.rationalHomSet κ (W'.map (frobenius κ p)) (W.map (frobenius κ p)) ∧
      ψF.comp (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) =
        (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W')).comp ψ ∧
      ψF'.comp (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W')) =
        (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)).comp ψ' ∧
      ψF'.comp ψF = (N : ℕ) • AddMonoidHom.id _ ∧ ψF.comp ψF' = (N : ℕ) • AddMonoidHom.id _ ∧
      ψF.ker = ψ.ker.map (WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_frobenius_conjugate_dualPair_mem_rationalHomSet.solution
