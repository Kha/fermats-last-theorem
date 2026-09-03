import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem AlgebraicGeometry.exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f]
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hxy : x ≠ y) :
    ∃ (U V : G.Opens) (hx : ⊤ ≤ x.1 ⁻¹ᵁ U) (hy : ⊤ ≤ y.1 ⁻¹ᵁ V) (n : ℕ) (a : Fin n → Γ(G, U)) (b : Fin n → Γ(G, V)),
      (∑ i : Fin n, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((x.1.appLE U ⊤ hx) (a i)) * (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((y.1.appLE V ⊤ hy) (b i)) ≠ 0) ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hPU : ⊤ ≤ P.1 ⁻¹ᵁ U) (hPV : ⊤ ≤ P.1 ⁻¹ᵁ V),
        ∑ i : Fin n, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hPU) (a i)) * (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE V ⊤ hPV) (b i)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_sum_appLE_mul_appLE_ne_zero_and_forall_eq_zero_of_ne_of_isSeparated.solution
