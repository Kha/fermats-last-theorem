import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.finite_and_finrank_kerAlgebra_varpi
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) :
    Module.Finite k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) ∧
      Module.finrank k (MvPowerSeries (Fin 2) k ⧸ Ideal.span (Set.range X₀.varpi)) = q ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi.solution
