import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem

set_option autoImplicit false

universe u

open FormalGroup

theorem FormalGroup.exists_ringHom_mvPowerSeries_eval_of_mem
    {A T : Type u} [CommRing A] [CommRing T] (f : A →+* T) (I : Ideal T) [IsAdicComplete I T]
    (ζ₀ ζ₁ : T) (h₀ : ζ₀ ∈ I) (h₁ : ζ₁ ∈ I) :
    ∃ e : MvPowerSeries (Fin 2) A →+* T,
      (∀ a : A, e (MvPowerSeries.C a) = f a) ∧ e (MvPowerSeries.X 0) = ζ₀ ∧ e (MvPowerSeries.X 1) = ζ₁ ∧
      (∀ (F : FormalGroup A) (G : FormalGroup T), F.IsBaseChange f G →
        (letI : WithIdeal T := ⟨I⟩; G.eval ζ₀ ζ₁) = e F.toPowerSeries) ∧
      (∀ (p : PowerSeries A) (i : Fin 2),
        e (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) p) =
          (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries (PowerSeries.map f p) (if i = 0 then ζ₀ else ζ₁))) ∧
      (∀ (n : ℕ) (F : MvPowerSeries (Fin 2) A), (∀ d : Fin 2 →₀ ℕ, d 0 + d 1 < n → MvPowerSeries.coeff d F = 0) →
        e F ∈ I ^ n) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem.solution
