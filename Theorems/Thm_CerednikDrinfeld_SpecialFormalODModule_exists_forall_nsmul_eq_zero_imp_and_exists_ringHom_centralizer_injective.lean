import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
attribute [-instance] CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm
attribute [-simp] CerednikDrinfeld.Standard.emb_inr CerednikDrinfeld.BoxBasisLemma.toFinsupp_apply CerednikDrinfeld.Standard.chi_zero CerednikDrinfeld.Standard.emb_inl CerednikDrinfeld.Standard.chi_one

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) :
    ∃ Φ₀ : CerednikDrinfeld.SpecialFormalODModule p j,
      (∀ f : MvFormalGroup.CartierModule p Φ₀.F, p • f = 0 → f = 0) ∧
      ∃ θ : Subring.centralizer
            (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) →+*
          Matrix (Fin 2) (Fin 2) ℚ_[p],
        Function.Injective θ ∧
        ∃ m : ℕ,
          (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective.solution
