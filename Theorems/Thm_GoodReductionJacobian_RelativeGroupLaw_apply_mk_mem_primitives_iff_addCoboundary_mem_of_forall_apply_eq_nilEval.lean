import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (F : MvFormalGroup 2 K) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Fin 2 → MvPowerSeries (Fin 2) K)
    (H : Type) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)

    (ν : ℕ) (Φ : (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ)) ≃ₐ[K] H)
    (hpin : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : H →ₐ[K] T),
      (∃ J : Ideal T, J ^ (ν + 1) = ⊥ ∧
        ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J) ∧
      (∀ G : MvPowerSeries (Fin 2) K,
        χ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval ν G (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) ∧
      ((e T (.toConv χ)).val : SchemeHomOver _ f) =
        θ T (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))))
    (hsurj : ∀ (T : Type) [CommRing T] [Algebra K T] (J : Ideal T) (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → T, (∀ i, s i ∈ J) → (∀ i, MvFormalGroup.nilEval m (φ i) s = 0) →
        ∃ χ : H →ₐ[K] T, ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) = s i)
    (G : MvPowerSeries (Fin 2) K) :
    Φ (Ideal.Quotient.mk _ G) ∈ primitives K H ↔
      (MvPowerSeries.constantCoeff G = 0 ∧
        F.addCoboundary G ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval.solution
