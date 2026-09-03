import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot

set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct

theorem IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot
    {𝒪 P : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    [CommRing P] [IsLocalRing P] [IsReduced P] [Algebra 𝒪 P] [Module.Finite 𝒪 P]
    [Module.IsTorsionFree 𝒪 P] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, P →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ ⨅ i, RingHom.ker (χ i).toRingHom = ⊥ ∧
        ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : ∀ i, A i, ∃ x : P, ∀ i, χ i x = a • y i := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot.solution
