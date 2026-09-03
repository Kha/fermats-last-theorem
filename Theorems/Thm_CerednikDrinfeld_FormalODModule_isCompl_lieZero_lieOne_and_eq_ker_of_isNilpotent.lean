import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent
    (p : ℕ) [Fact p.Prime] (ω : Zp2 p) (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0)
    (hω : ω * ω = (t : Zp2 p) * ω - (n : Zp2 p)) (hσ : WittVector.frobenius ω = (t : Zp2 p) - ω)
    (hdense : ∀ (k : ℕ) (x : Zp2 p), ∃ c d : ℤ, x - ((c : Zp2 p) + (d : Zp2 p) * ω) ∈ Ideal.span {((p : Zp2 p)) ^ k})
    {S : Type} [CommRing S] (hS : IsNilpotent (p : S)) (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    IsUnit (j ω - j (WittVector.frobenius ω)) ∧
    (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S)) *
        (MvFormalGroup.linearPart (Y.act ω) - j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S)) = 0 ∧
    Y.lieZero j = LinearMap.ker (Matrix.mulVecLin
        (MvFormalGroup.linearPart (Y.act ω) - j ω • (1 : Matrix (Fin 2) (Fin 2) S))) ∧
    Y.lieOne j = LinearMap.ker (Matrix.mulVecLin
        (MvFormalGroup.linearPart (Y.act ω) - j (WittVector.frobenius ω) • (1 : Matrix (Fin 2) (Fin 2) S))) ∧
    IsCompl (Y.lieZero j) (Y.lieOne j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_and_eq_ker_of_isNilpotent.solution
