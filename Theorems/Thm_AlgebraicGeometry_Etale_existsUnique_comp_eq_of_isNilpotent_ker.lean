import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.existsUnique_comp_eq_of_isNilpotent_ker
    {X Y T T₀ : Scheme.{0}} (q : Y ⟶ X) [Etale q] (k : T₀ ⟶ T) [IsClosedImmersion k] (hk : IsNilpotent k.ker)
    (t : T ⟶ X) (s₀ : T₀ ⟶ Y) (hs₀ : s₀ ≫ q = k ≫ t) :
    ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker.solution
