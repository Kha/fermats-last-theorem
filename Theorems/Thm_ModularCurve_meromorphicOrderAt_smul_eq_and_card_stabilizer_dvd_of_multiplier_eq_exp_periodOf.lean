import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import P2M.Util
import P2M.Sol.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf

open UpperHalfPlane
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ) :
    (∀ (γ : Γ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
    (∀ (τ : ℍ) (n : ℤ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) →
        (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) ∣ 2 * n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.solution
