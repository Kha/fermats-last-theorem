import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (𝒱 : X.TwoAffineOpenCover)
    [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    (ω : ↥((𝒱.kaehlerSections c).H0)) (ω₀ : Ω[(𝒱.cover c).A0⁄R]) (ω₁ : Ω[(𝒱.cover c).A1⁄R])
    (h0 : ω.val.1 = ϖ • ω₀) (h1 : ω.val.2 = ϖ • ω₁) :
    ∃ ω' : ↥((𝒱.kaehlerSections c).H0), ω = ϖ • ω' ∧ ω'.val = (ω₀, ω₁) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_eq_smul_kaehlerH0_and_val_eq_of_val_eq_smul.solution
