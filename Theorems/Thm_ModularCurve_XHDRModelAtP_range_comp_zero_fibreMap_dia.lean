import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_range_comp_zero_fibreMap_dia

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRModelAtP.range_comp_zero_fibreMap_dia
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (d : (ZMod M)ˣ) :
    Set.range ((𝔓.comp A hA ρ hρ 0 ≫
        fibreMap (overOfIso (𝔓.dia d) (𝔓.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ)).base) =
      Set.range (𝔓.comp A hA ρ hρ 0).base := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_range_comp_zero_fibreMap_dia.solution
