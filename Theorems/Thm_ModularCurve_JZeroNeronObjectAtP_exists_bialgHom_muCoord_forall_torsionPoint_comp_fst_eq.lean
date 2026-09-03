import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2)
    (H : Type) [CommRing H] [HopfAlgebra ↥A H]
    (e : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      WithConv (H →ₐ[↥A] T) ≃
        (Λ.L.baseChange Λ.σA).torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥A T))) m)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra ↥A T] (φ ψ : WithConv (H →ₐ[↥A] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) =
        (Λ.L.baseChange Λ.σA).mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra ↥A T] [CommRing T'] [Algebra ↥A T']
        (a : T →ₐ[↥A] T') (φ : WithConv (H →ₐ[↥A] T)),
      ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1) :
    ∃ φ : H →ₐc[↥A] muCoord ↥A O.toricRank m,
      ∀ (T : Type) [CommRing T] [Algebra ↥A T] (ψ : muCoord ↥A O.toricRank m →ₐ[↥A] T),
        ((e T (.toConv (ψ.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m)))).val :
            SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 ≫ pullback.fst Λ.f Λ.σA =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫
            (O.degeneracyHom i).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq.solution
