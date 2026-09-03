import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
    {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharP k q]
    (j : Zp2 q →+* k) (X₀ : SpecialFormalODModule q j) :
    (∀ m ∈ X₀.toFormalODModule.lieZero j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∨
      (∀ m ∈ X₀.toFormalODModule.lieOne j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne.solution
