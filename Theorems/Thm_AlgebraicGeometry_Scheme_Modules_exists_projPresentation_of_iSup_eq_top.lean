import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤))
    (U : Fin (N + 1) → X.Opens) (hU : iSup U = ⊤)
    (hframe : ∀ i (V : X.Opens), V ≤ U i →
       Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧ ∀ i, U i ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.solution
