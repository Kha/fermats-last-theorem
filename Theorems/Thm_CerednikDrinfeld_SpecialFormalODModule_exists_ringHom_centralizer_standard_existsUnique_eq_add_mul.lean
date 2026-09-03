import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_LubinTateModule
import Definitions.Def_CerednikDrinfeld_StandardFormalODModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul

set_option autoImplicit false

universe u

open CerednikDrinfeld in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (j : Zp2 p →+* k) :
    ∃ (A : Zp2 p →+*
          Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd}))
      (Ψ : Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd})),
      (∀ a, (A a : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 0 (LubinTate.rho j a) + Standard.cell j 1 1 (LubinTate.rho j a)) ∧
      (Ψ : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 1 (LubinTate.rho j (p : Zp2 p) * LubinTate.phi j) +
            Standard.cell j 1 0 (LubinTate.phi j) ∧
      Ψ * Ψ = A ((p : Zp2 p) ^ 2) ∧
      (∀ a, Ψ * A a = A (WittVector.frobenius a) * Ψ) ∧
      ∀ e, ∃! ac : Zp2 p × Zp2 p, e = A ac.1 + A ac.2 * Ψ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul.solution
