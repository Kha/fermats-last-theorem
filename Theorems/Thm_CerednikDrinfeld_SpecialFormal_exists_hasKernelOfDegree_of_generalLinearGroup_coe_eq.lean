import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r])))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e) :
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq.solution
