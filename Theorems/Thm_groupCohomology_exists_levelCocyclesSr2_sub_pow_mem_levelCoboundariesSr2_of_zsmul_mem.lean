import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_GaloisSUnits
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S)
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hUS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧ F₀.fixingSubgroup ≤ U)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p) (hζS : ζ ∈ galoisSUnits S) (hU : ∀ σ ∈ U, σ • ζ = ζ)
    (X : ↥U × ↥U → Additive ↥(galoisSUnits S))
    (hX : X ∈ levelCocyclesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S)))
    (hpX : (p : ℤ) • X ∈ levelCoboundariesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S))) :
    ∃ z : ↥U × ↥U → ZMod p, z ∈ levelCocyclesSr₂ U.subtype S (Rep.trivial (ZMod p) ↥U (ZMod p)) ∧
      X - (fun g => Additive.ofMul (⟨ζ ^ (z g).val, Subgroup.pow_mem _ hζS _⟩ : ↥(galoisSUnits S))) ∈
        levelCoboundariesSr₂ U.subtype S (Rep.res U.subtype (galoisSUnitsRep S)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_levelCocyclesSr2_sub_pow_mem_levelCoboundariesSr2_of_zsmul_mem.solution
