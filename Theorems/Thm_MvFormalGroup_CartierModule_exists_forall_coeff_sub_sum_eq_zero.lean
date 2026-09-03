import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_forall_coeff_sub_sum_eq_zero
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (t : ℕ → MvFormalGroup.CartierModule p Φ) (N : ℕ → ℕ) (hN : Monotone N)
    (hN' : ∀ B : ℕ, ∃ K, B ≤ N K)
    (ht : ∀ (k : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N k → MvPowerSeries.coeff e ((t k).toPowerSeries j) = 0) :
    ∃ s : MvFormalGroup.CartierModule p Φ, ∀ (K : ℕ) (j : Fin d) (e : ℕ →₀ ℕ),
      Finsupp.weight (fun m : ℕ => p ^ m) e < N K →
        MvPowerSeries.coeff e ((s - ∑ k ∈ Finset.range K, t k).toPowerSeries j) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_forall_coeff_sub_sum_eq_zero.solution
