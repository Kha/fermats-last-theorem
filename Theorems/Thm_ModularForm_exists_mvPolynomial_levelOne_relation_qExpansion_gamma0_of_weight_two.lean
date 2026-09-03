import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularForm_exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open UpperHalfPlane

theorem ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two
    (p : ℕ) [Fact p.Prime] (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (b : ℕ → ℤ)
    (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n) :
    ∃ (c : ℤ) (P : ℕ → MvPolynomial (Fin 2) ℤ), c ≠ 0 ∧ P 0 = MvPolynomial.C c ∧
      (∀ r : ℕ, (P r).IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (2 * r)) ∧
      ∀ (R : Type) [CommRing R],
        ∑ r ∈ Finset.range (p + 2),
          (-1) ^ r *
            MvPolynomial.aeval
              (![ModularCurve.qExpand R p
                  (HahnSeries.ofPowerSeries ℤ R
                    (PowerSeries.map (Int.castRingHom R) ModularCurve.eisenstein4)),
                 ModularCurve.qExpand R p
                  (HahnSeries.ofPowerSeries ℤ R
                    (PowerSeries.map (Int.castRingHom R) ModularCurve.eisenstein6))]
                : Fin 2 → LaurentSeries R) (P r) *
            HahnSeries.ofPowerSeries ℤ R ((PowerSeries.mk b).map (Int.castRingHom R)) ^ (p + 1 - r)
          = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two.solution
