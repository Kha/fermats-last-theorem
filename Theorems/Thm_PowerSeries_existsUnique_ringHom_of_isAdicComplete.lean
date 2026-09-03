import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_existsUnique_ringHom_of_isAdicComplete

theorem PowerSeries.existsUnique_ringHom_of_isAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) :
    ∃! φ : PowerSeries A →+* S,
      ∀ (F : PowerSeries A) (n : ℕ),
        φ F - (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_existsUnique_ringHom_of_isAdicComplete.solution
