import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log

set_option autoImplicit false

universe u
open MvPowerSeries in

theorem MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
    (p : ℕ) [Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
    (f ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hf0 : ∀ i, (f i).constantCoeff = 0)
    (hf1 : ∀ i j : Fin d, (coeff (Finsupp.single j 1) (f i) : 𝓞) = if i = j then 1 else 0)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hfψ : ∀ i, subst ψ (f i) = X i) (hψf : ∀ i, subst f (ψ i) = X i)
    (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))
    (c : ℕ → Fin d → 𝓞) :
    ∃ m : MvFormalGroup.CartierModule p Φ,
      (∀ j, MvFormalGroup.CartierModule.tangent m j = c 0 j) ∧
      (∀ (j : Fin d) (k n : ℕ),
        (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : 𝓞) = (p : 𝓞) ^ k * c (k + n) j) ∧
      (∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
        (coeff e (subst m.toPowerSeries (f j)) : 𝓞) = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log.solution
