import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u in

theorem WeierstrassCurve.heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient
    {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (N : ℕ) (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf (reduceHom hΔ Q) = N)
    (W' : WeierstrassCurve A)
    (hW' : W'.map A.subtype = (W.map A.subtype).fullKernelQuotient Q N)
    (hW'red : W'.map (residue A) = (W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N)
    (hΔ' : (W'.map (residue A)).Δ ≠ 0)
    (φ : (W.map A.subtype).toAffine.Point →+
      ((W.map A.subtype).fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : (W.map A.subtype).toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ₀ : (W.map (residue A)).toAffine.Point →+
      ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N).toAffine.Point)
    (hφ₀ker : φ₀.ker = AddSubgroup.zmultiples (reduceHom hΔ Q))
    (hφ₀ : ∀ P : (W.map (residue A)).toAffine.Point, P ∉ AddSubgroup.zmultiples (reduceHom hΔ Q) →
      (φ₀ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • reduceHom hΔ Q).coordsOrZero.1 - (k • reduceHom hΔ Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • reduceHom hΔ Q).coordsOrZero.2 - (k • reduceHom hΔ Q).coordsOrZero.2)))
    (P : (W.map A.subtype).toAffine.Point) (P' : (W'.map A.subtype).toAffine.Point)
    (hP' : HEq P' (φ P)) :
    HEq (reduceHom hΔ' P') (φ₀ (reduceHom hΔ P)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_heq_reduceHom_fullKernelHom_of_map_eq_fullKernelQuotient.solution
