import Definitions.Def_CuspForm_HeckeAlgebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_CuspForm_heckeAlgebra_exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.heckeAlgebra.exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (N : ℕ) [NeZero N] (S : Set ℕ)
    (F : Type) [Field F] [Algebra 𝒪 F] (hF : Function.Injective (algebraMap 𝒪 F))
    (χ : CuspForm.heckeAlgebra N 2 S →+* F)
    (c : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ResidueField 𝒪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      ∃ P : 𝒪[X], P.Monic ∧ (P.map (algebraMap 𝒪 F)).IsRoot (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
        P.map (residue 𝒪) = (X - C (c ℓ hℓ hℓN hℓS)) ^ P.natDegree)
    (d : ∀ (q : ℕ), q.Prime → q ∣ N → q ∉ S → ResidueField 𝒪)
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      ∃ P : 𝒪[X], P.Monic ∧ (P.map (algebraMap 𝒪 F)).IsRoot (χ (CuspForm.heckeAlgebra.U hq hqN hqS)) ∧
        P.map (residue 𝒪) = (X - C (d q hq hqN hqS)) ^ P.natDegree) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪'))
      (_ : CharZero 𝒪') (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')) (e : 𝒪' →+* F),
    Function.Injective e ∧ e.comp (algebraMap 𝒪 𝒪') = algebraMap 𝒪 F ∧
    ∃ (χ' : CuspForm.heckeAlgebra N 2 S →+* 𝒪') (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪),
      e.comp χ' = χ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = c ℓ hℓ hℓN hℓS) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        θ (CuspForm.heckeAlgebra.U hq hqN hqS) = d q hq hqN hqS) ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        residue 𝒪' (χ' t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ t) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_comp_eq_and_residue_eq_of_forall_isRoot_of_map_residue_eq_pow.solution
