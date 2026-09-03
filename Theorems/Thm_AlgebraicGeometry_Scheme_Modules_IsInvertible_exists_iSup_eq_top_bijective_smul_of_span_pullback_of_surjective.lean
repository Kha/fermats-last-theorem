import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
    {X X' : Scheme.{u}} (c : X' ⟶ X) [Surjective c]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) {N : ℕ} (σ : Fin (N + 1) → Γ(L, ⊤))

    (σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ l))
    {M : ℕ} (ρ : Fin (M + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (U' : Fin (M + 1) → X'.Opens) (hU' : iSup U' = ⊤)
    (hframe' : ∀ (j : Fin (M + 1)) (V' : X'.Opens), V' ≤ U' j →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback c).obj L).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (ρ j) :
          Γ((Scheme.Modules.pullback c).obj L, V')))
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → Γ(X', ⊤), ρ j = ∑ l, a l • σ' l) :
    ∃ U : Fin (N + 1) → X.Opens, iSup U = ⊤ ∧
      ∀ (l : Fin (N + 1)) (V : X.Opens), V ≤ U l →
        Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l) : Γ(L, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective.solution
