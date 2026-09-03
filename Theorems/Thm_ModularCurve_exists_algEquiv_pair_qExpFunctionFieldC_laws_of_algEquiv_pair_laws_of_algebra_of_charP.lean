import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
    (p Q : ℕ) [Fact p.Prime] [NeZero Q] (H' : Subgroup (ZMod Q)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (κ : Type*) [Field κ] [Algebra κ K]
    (q : ℕ) (hq : q.Prime) (hQK : ((Q : ℕ) : K) ≠ 0) (hqK : ((q : ℕ) : K) ≠ 0)
    (hβκ : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined κ Q H' q)
    (hβK : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined K Q H' q)
    (φκ : ↥(integralClosure ℤ ℂ) →+* κ)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])
    (WQq : GL (Fin 2) ℝ) (hWQq : (WQq : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q * q : ℕ) : ℝ), 0])
    (σκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')))
    (τκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[κ]
        ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))))
    (hκ : haveI : NeZero q := ⟨hq.ne_zero⟩;

      (∀ x, τκ (ModularCurve.heckeAlphaModLH κ Q H' q x) = ModularCurve.heckeBetaModLH κ Q H' q (σκ x)) ∧

      (∀ x, τκ (ModularCurve.heckeBetaModLH κ Q H' q x) = ModularCurve.heckeAlphaModLH κ Q H' q (σκ x)) ∧

      (∀ x, σκ (σκ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((σκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H'))) : LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ)) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((τκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ))) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')))
      (τ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))),

      (∀ x, τ (ModularCurve.heckeAlphaModLH K Q H' q x) = ModularCurve.heckeBetaModLH K Q H' q (σ x)) ∧

      (∀ x, τ (ModularCurve.heckeBetaModLH K Q H' q x) = ModularCurve.heckeAlphaModLH K Q H' q (σ x)) ∧

      (∀ x, σ (σ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H'))) : LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((τ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.solution
