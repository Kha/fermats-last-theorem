import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (PA QA PB QB : Polynomial K) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (h : ((∀ α ∈ QA.roots, Valued.v α < 1) ∧ ∀ β ∈ QB.roots, 1 ≤ Valued.v β) ∨
      ((∀ α ∈ QA.roots, Valued.v α ≤ 1) ∧ ∀ β ∈ QB.roots, 1 < Valued.v β)) :
    (PA * QB + PB * QA).support.sup (fun i => Valued.v ((PA * QB + PB * QA).coeff i)) =
      max ((PA * QB).support.sup fun i => Valued.v ((PA * QB).coeff i))
        ((PB * QA).support.sup fun i => Valued.v ((PB * QA).coeff i)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles.solution
