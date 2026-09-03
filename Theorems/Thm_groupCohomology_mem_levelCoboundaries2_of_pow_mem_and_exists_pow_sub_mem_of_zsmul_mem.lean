import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem
    {p : ℕ} [Fact p.Prime] (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p) (hD : ∀ σ ∈ D, σ • ζ = ζ) :
    (∀ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) →
      (fun g => Additive.ofMul (ζ ^ (z g).val) : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ) ∈
        levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      z ∈ levelCoboundaries₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p))) ∧
    (∀ X : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ,
      X ∈ levelCocycles₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))) →
      ∃ z : ↥D × ↥D → ZMod p, z ∈ levelCocycles₂ D.subtype (Rep.trivial (ZMod p) ↥D (ZMod p)) ∧
        X - (fun g => Additive.ofMul (ζ ^ (z g).val)) ∈
          levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_levelCoboundaries2_of_pow_mem_and_exists_pow_sub_mem_of_zsmul_mem.solution
