import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f] {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) :
    ∀ (v₀ : Fin g → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G.Opens) (fs : Finset (Γ(G, U))) (ε : ℝ) (h₀ : ⊤ ≤ (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e P = (w : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated.solution
