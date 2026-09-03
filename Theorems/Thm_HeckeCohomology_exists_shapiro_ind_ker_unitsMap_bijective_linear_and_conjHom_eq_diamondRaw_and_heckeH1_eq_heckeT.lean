import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import P2M.Util
import P2M.Sol.S_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT

set_option autoImplicit false

theorem
HeckeCohomology.exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (κ : Type) [Field κ]
    (lift : CongruenceSubgroup.Gamma0 (N * q) → CongruenceSubgroup.Gamma0 N)
    (hlift : ∀ σ, ((lift σ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ Φ : groupCohomology.H1
        (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))) →+
        CohCarrier.H1 (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ,
      Function.Bijective Φ ∧
      (∀ (c : κ) x, Φ (c • x) = c • Φ x) ∧
      (∀ (σ : CongruenceSubgroup.Gamma0 (N * q))
          (c : Rep.res (CohCarrier.conjHom N ⊥ (lift σ))
              (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
                ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp
                  (CohCarrier.GammaH N ⊥).subtype)))) ⟶
            Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype)))),
        (∀ v, c.hom v =
          CuspidalType.ind q κ
            (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))
              (lift σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)))⁻¹ v) →
        ∀ x, Φ (groupCohomology.map (CohCarrier.conjHom N ⊥ (lift σ)) c 1 x) =
          CohCarrier.diamondRaw (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker κ σ (Φ x)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q → ∀ (u : (ZMod q)ˣ), (u : ZMod q) = ℓ →
        ∀ (hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ)
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))
            (CuspidalType.ind q κ (CuspidalType.diagElem q u)))
          (x : groupCohomology.H1
            (Rep.of ((CuspidalType.ind q κ).comp (Matrix.SpecialLinearGroup.toGL.comp
              ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (CohCarrier.GammaH N ⊥).subtype))))),
          Φ (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) _ _ hφ x) =
            CohCarrier.heckeT (N * q) (ZMod.unitsMap (dvd_mul_right N q)).ker ℓ κ (Φ x) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_exists_shapiro_ind_ker_unitsMap_bijective_linear_and_conjHom_eq_diamondRaw_and_heckeH1_eq_heckeT.solution
