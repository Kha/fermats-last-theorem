import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke
import Definitions.Def_GroupCohomology_DClassCoeff
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem HeckeEis.exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (κ : Type) [Field κ]
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (hV : ∀ v : V, (∀ g : SL(2, ZMod q), ρ (Matrix.SpecialLinearGroup.toGL g) v = v) → v = 0)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    ∃ hφ : ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
        HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
          (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id),
      ∃ y : groupCohomology.H1
          (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))),
        y ≠ 0 ∧
        (∀ (σ : ↥(Gamma0 N))
            (c : Rep.res (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ)
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ))))) ⟶
              (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))),
            (∀ v : V, c.hom v = ρ (((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) σ)⁻¹ v) →
            groupCohomology.map (CohCarrier.conjHom N (⊥ : Subgroup (ZMod N)ˣ) σ) c 1 y = y) ∧
        ∀ i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ insert q S₀},
          haveI : NeZero (i.1 : ℕ) := ⟨i.2.1.ne_zero⟩
          HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ i.1) (HeckeCohomology.cTop N ⊥ i.1)
            (Rep.of ((ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)).comp
              (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 (M := N) (⊥ : Subgroup (ZMod N)ˣ)))))
            (if h : (((i.1 : ℕ) : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 ((i.1 : ℕ) : ZMod q) h))
            else LinearMap.id)
            (hφ i) y = lam i.1 • y := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_ne_zero_map_conjHom_eq_and_heckeH1_gammaH_bot_eq_smul_of_isEigensystemH1.solution
