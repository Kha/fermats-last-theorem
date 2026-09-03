import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_perfectPairing_parabolicHoms_baseChange
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ)
    (hIP : Function.Bijective IP) (hIPf : Function.Bijective IP.flip)
    (R : Type*) [CommRing R] [IsAddTorsionFree R] :
    ∃ B : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] R,
      Function.Bijective B ∧ Function.Bijective B.flip ∧
      (∀ (x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' y' : ModularCurve.Period.parabolicHoms R Γ R),
        ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        ((y' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        B x' y' = (IP x y : R)) ∧
      (∀ (T T' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ)
          (S S' : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R),
        (∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, IP (T x) y = IP x (T' y)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S' x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T' x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        ∀ x' y' : ModularCurve.Period.parabolicHoms R Γ R, B (S x') y' = B x' (S' y')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange.solution
