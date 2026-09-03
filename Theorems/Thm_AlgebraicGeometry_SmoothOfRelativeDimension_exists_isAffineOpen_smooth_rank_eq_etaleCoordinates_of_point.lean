import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
    {k : Type} [Field k] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of k)) {n : ℕ}
    (hsm : SmoothOfRelativeDimension n πM)
    (σ : Spec (CommRingCat.of k) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U),
      letI := πM.sectionsAlgebra U
      IsDomain Γ(M, U) ∧ Algebra.FiniteType k Γ(M, U) ∧ Algebra.Smooth k Γ(M, U) ∧
      Module.rank Γ(M, U) (KaehlerDifferential k Γ(M, U)) = n ∧
      ∃ (σ₀ : Γ(M, U) →ₐ[k] k) (t : Fin n → Γ(M, U)),
        (∀ s : Γ(M, U), σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((σ.appLE U ⊤ hσU) s)) ∧
        (∀ i : Fin n, σ₀ (t i) = 0) ∧
        (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule Γ(M, U) (KaehlerDifferential k Γ(M, U))) ⊔
          Submodule.span Γ(M, U) (Set.range fun i : Fin n => KaehlerDifferential.D k Γ(M, U) (t i)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point.solution
