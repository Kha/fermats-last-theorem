import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem AlgebraicGeometry.exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f]
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hxy : x ≠ y) :
    ∃ (U V : G.Opens) (hx : ⊤ ≤ x.1 ⁻¹ᵁ U) (hy : ⊤ ≤ y.1 ⁻¹ᵁ V)
      (fsU : Finset (Γ(G, U))) (fsV : Finset (Γ(G, V))) (ε : ℝ), 0 < ε ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hPU : ⊤ ≤ P.1 ⁻¹ᵁ U) (hPV : ⊤ ≤ P.1 ⁻¹ᵁ V),
        (∀ φ ∈ fsU, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hPU) φ) -
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((x.1.appLE U ⊤ hx) φ)‖ < ε) →
        (∀ ψ ∈ fsV, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE V ⊤ hPV) ψ) -
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((y.1.appLE V ⊤ hy) ψ)‖ < ε) → False := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated.solution
