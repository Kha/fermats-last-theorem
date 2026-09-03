import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms
    (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (hpN : Nat.Coprime p N)
    (K : Type*) [Field K] :
    ∃ S : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) ≃ₗ[K]
        ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K),

      (∀ (z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)))
          (γ : CongruenceSubgroup.Gamma0 (N * p)),
        ((S (HeckeEis.coeffH1parMk _ z) :
            ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
            Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K) (Additive.ofMul γ)
          = (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ)
              (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧)) ∧

      (∀ (ℓ : ℕ) [NeZero ℓ], Nat.Coprime ℓ (N * p) →
        ∃ T' : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[K]
            HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              (w : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
                  = HeckeEis.coeffHeckeFun N ℓ
                      ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)
                      (HeckeEis.projLineAlphaAdj p K ℓ) z ∧
              T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
          ∀ x, ((S (T' x) : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                  Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
              = HeckeEis.heckeOperatorHom (N * p) ℓ K
                  ((S x : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                    Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)) ∧

      (∀ φ : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
              = (fun g _ => (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K) (Additive.ofMul g)) ∧
          ((S (HeckeEis.coeffH1parMk _ z) :
              ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
              Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
            = HeckeEis.pullbackHom (Ihara.ι₀ N p) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms.solution
