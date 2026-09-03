import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_baseChange
    (R : Type) [CommRing R] (π : R) (q : ℕ) (S : Type) [CommRing S] [Algebra R S] :
    ∃ φ : chartERing R π q →+* chartERing S (algebraMap R S π) q,
      φ.comp (algebraMap R (chartERing R π q)) = (algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S) ∧
      φ (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q ∧
      φ (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q ∧
      IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R (chartERing R π q)))
        (CommRingCat.ofHom (algebraMap S (chartERing S (algebraMap R S π) q))) (CommRingCat.ofHom φ) ∧
      ∀ φ' : chartERing R π q →+* chartERing S (algebraMap R S π) q,
        φ'.comp (algebraMap R (chartERing R π q)) = (algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S) →
        φ' (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q →
        φ' (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q → φ' = φ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange.solution
