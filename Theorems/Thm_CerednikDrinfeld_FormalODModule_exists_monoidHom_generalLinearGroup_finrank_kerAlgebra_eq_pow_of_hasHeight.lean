import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
    {r : ℕ} [Fact r.Prime] (K : Type u) [Field K] [CharP K r]
    (Φ : FormalODModule r K) (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) :
    ∃ ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ,
      (∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r],
        (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) →
          ν g = Multiplicative.ofAdd (4 : ℤ)) ∧
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
        (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∃ h : ℕ, ν g = Multiplicative.ofAdd (h : ℤ) ∧
          Module.Finite K (FormalODModule.KerAlgebra (e : MvFormalGroup.End Φ.F).toPowerSeries) ∧
          ∀ (κ : Type u) [Field κ] (f : K →+* κ),
            Module.finrank κ
              (FormalODModule.KerAlgebra (Series.map f (e : MvFormalGroup.End Φ.F).toPowerSeries)) =
              r ^ h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight.solution
