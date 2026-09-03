import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (F : MvFormalGroup 2 K) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Fin 2 → MvPowerSeries (Fin 2) K)
    (H : Type) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)

    (ν : ℕ) (Φ : (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ)) ≃ₐ[K] H)
    (hpin : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : H →ₐ[K] T),
      (∃ J : Ideal T, J ^ (ν + 1) = ⊥ ∧
        ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J) ∧
      (∀ G : MvPowerSeries (Fin 2) K,
        χ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval ν G (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) ∧
      ((e T (.toConv χ)).val : SchemeHomOver _ f) =
        θ T (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))))

    (act : A ⟶ A)
    (S : Fin 2 → MvPowerSeries (Fin 2) K) (hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0)
    (hS : ∀ (T : Type) [CommRing T] [Algebra K T] (J : Ideal T) (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → T, (∀ i, s i ∈ J) →
        (θ T (fun i => MvFormalGroup.nilEval m (S i) s)).1 = (θ T s).1 ≫ act)
    (φH : H →ₐ[K] H)
    (hφH : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : WithConv (H →ₐ[K] T)),
      ((e T (.toConv (χ.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T χ).val.1 ≫ act)
    (G : MvPowerSeries (Fin 2) K) :
    φH (Φ (Ideal.Quotient.mk _ G)) = Φ (Ideal.Quotient.mk _ (MvPowerSeries.subst S G)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval.solution
