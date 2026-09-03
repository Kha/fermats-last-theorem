import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

theorem CohCarrier.exists_intMatrix_opFamily_basis_parabolicHoms
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) :
    ∃ (n K : ℕ) (T : CohCarrier.Gen M S → Matrix (Fin n) (Fin n) ℤ) (u : Fin K → Matrix (Fin n) (Fin n) ℤ)
      (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ) (cT : CohCarrier.Gen M S → Fin K → ℤ),
      (∀ k l : Fin K, u k * u l = ∑ m, c k l m • u m) ∧
      (∑ m, c₁ m • u m = 1) ∧
      (∀ g : CohCarrier.Gen M S, ∑ m, cT g m • u m = T g) ∧
      (∀ k : Fin K, u k ∈ Algebra.adjoin ℤ (Set.range T)) ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R],
        LinearIndependent R (fun k : Fin K => (u k).map (Int.castRingHom R)) ∧
        Submodule.span R (Set.range fun k : Fin K => (u k).map (Int.castRingHom R)) =
          Subalgebra.toSubmodule
            (Algebra.adjoin R (Set.range fun g : CohCarrier.Gen M S => (T g).map (Int.castRingHom R))) ∧
        ∃ bR : Module.Basis (Fin n) R ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R),
          ∀ (g : CohCarrier.Gen M S) (j : Fin n),
            CohCarrier.opFamily M H S R g
                ((bR j : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) =
              ∑ i, ((T g i j : ℤ) : R) •
                ((bR i : ↥(ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) R)) :
                  CohCarrier.H1 M H R) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_intMatrix_opFamily_basis_parabolicHoms.solution
