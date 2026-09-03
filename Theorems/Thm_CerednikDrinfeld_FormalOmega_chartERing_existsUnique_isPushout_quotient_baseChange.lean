import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_quotient_baseChange
    (R : Type) [CommRing R] (π : R) (q n : ℕ) (S : Type) [CommRing S] [Algebra R S] :
    ∃ φ : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
        (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
      φ.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
        (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
          (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ∧
      φ (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) ∧
      φ (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) ∧
      IsPushout
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)}))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _))
        (CommRingCat.ofHom φ) ∧
      ∀ φ' : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
          (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
        φ'.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
          (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
              (algebraMap S (chartERing S (algebraMap R S π) q))
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
                S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
            (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) →
        φ' (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) →
        φ' (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) → φ' = φ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange.solution
