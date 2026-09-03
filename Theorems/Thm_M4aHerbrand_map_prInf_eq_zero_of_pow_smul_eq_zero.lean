import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import P2M.Util
import P2M.Sol.S_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]

    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (p : ℕ) [Fact p.Prime]
    (hinf2 : p = 2 → ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0)
    (v : InfinitePlace F) :
    (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) 2).hom x = 0 := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero.solution
