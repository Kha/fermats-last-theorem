import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
    {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T), D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst.solution
