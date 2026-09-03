import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul
    {X : Scheme.{u}} (M : X.Modules) {ι : Type*} [Fintype ι] (a : ι → Γ(X, ⊤)) (t : ι → Γ(M, ⊤)) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (∑ j, a j • t j) : Γ(M, V))) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t j) : Γ(M, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul.solution
