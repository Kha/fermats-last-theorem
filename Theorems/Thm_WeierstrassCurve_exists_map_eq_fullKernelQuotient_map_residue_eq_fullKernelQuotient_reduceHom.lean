import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

universe u in

theorem WeierstrassCurve.exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom
    {L : Type u} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    (N : ℕ) (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf (reduceHom hΔ Q) = N) :
    ∃ W' : WeierstrassCurve A,
      W'.map A.subtype = (W.map A.subtype).fullKernelQuotient Q N ∧
      W'.map (residue A) = (W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N ∧
      ∀ hΔ₀ : ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N).Δ ≠ 0,
        ∃ (hΔ' : ((W.map A.subtype).fullKernelQuotient Q N).Δ ≠ 0)
          (hmem : @WeierstrassCurve.j L _ ((W.map A.subtype).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ'⟩ ∈ A),
          residue A ⟨_, hmem⟩ =
            @WeierstrassCurve.j (ResidueField A) _
              ((W.map (residue A)).fullKernelQuotient (reduceHom hΔ Q) N)
              ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_eq_fullKernelQuotient_map_residue_eq_fullKernelQuotient_reduceHom.solution
