import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_map_eq_and_reduceHom_vcFun_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u in

theorem WeierstrassCurve.exists_variableChange_map_eq_and_reduceHom_vcFun_eq
    {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W₁ W₂ : WeierstrassCurve A} (hΔ₁ : (W₁.map (residue A)).Δ ≠ 0)
    (hΔ₂ : (W₂.map (residue A)).Δ ≠ 0)
    (C : VariableChange L) (hC : C • W₁.map A.subtype = W₂.map A.subtype) :
    ∃ (C₀ : VariableChange A), C₀ • W₁ = W₂ ∧ C₀.map A.subtype = C ∧
      (C₀.map (residue A)) • W₁.map (residue A) = W₂.map (residue A) ∧
      ∀ (P : (C • W₁.map A.subtype).toAffine.Point) (P₂ : (W₂.map A.subtype).toAffine.Point),
        HEq P P₂ →
        ∀ R : ((C₀.map (residue A)) • W₁.map (residue A)).toAffine.Point,
          HEq R (reduceHom hΔ₂ P₂) →
          reduceHom hΔ₁ (Point.vcFun C (W₁.map A.subtype) P) =
            Point.vcFun (C₀.map (residue A)) (W₁.map (residue A)) R := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_and_reduceHom_vcFun_eq.solution
