import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (x : AlgebraicClosure ℚ)
    (hx : x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra.Etale ℤ E) (ι : E →+* AlgebraicClosure ℚ) (φ₀ : E →+* ZMod p),
      (∀ e : E, ι e ∈ Pl) ∧
      (∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) ∧
      x ∈ Set.range ι := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup.solution
