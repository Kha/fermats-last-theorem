import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
namespace P2MW.S_ModularCurve_XHDRModelAtP_range_comp_zero_fibreMap_dia

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (d : (ZMod M)ˣ) :
    Set.range ((𝔓.comp A hA ρ hρ 0 ≫
        fibreMap (overOfIso (𝔓.dia d) (𝔓.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ)).base) =
      Set.range (𝔓.comp A hA ρ hρ 0).base := by
  rw [𝔓.comp_dia A hA ρ hρ 0 d]
  set f := fibreMap (Γ := ΓN p M H hpM) (hj := hj)
    (overOfIso (𝔓.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) (𝔓.dia0_over _))
    ((IsLocalRing.residue ↥A).comp ρ) with hf
  haveI : IsIso f := by
    rw [hf]
    dsimp only [fibreMap, overOfIso]
    infer_instance
  have hsurj : Function.Surjective f.base := f.surjective
  have hcomp : (⇑(f ≫ 𝔓.comp A hA ρ hρ 0) : _ → _) = ⇑(𝔓.comp A hA ρ hρ 0) ∘ ⇑f := by
    funext x
    exact Scheme.Hom.comp_apply f _ x
  rw [hcomp]
  exact hsurj.range_comp _
