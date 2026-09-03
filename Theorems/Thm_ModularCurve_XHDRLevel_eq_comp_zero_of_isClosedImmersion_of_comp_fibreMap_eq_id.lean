import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRLevel_eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (κ : Type) [Field κ] (toκ : R p →+* κ)
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)]
    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ))
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_jointly_surjective : ∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base)
    (comp_pi : comp 0 ≫ fibreMap π toκ = 𝟙 _)
    (hnosec : ∀ β : fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ,
      β ≫ comp 1 ≫ fibreMap π toκ ≠ 𝟙 _)
    (s : fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ)
    (hs : IsClosedImmersion s) (hsπ : s ≫ fibreMap π toκ = 𝟙 _) :
    s = comp 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRLevel_eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id.solution
