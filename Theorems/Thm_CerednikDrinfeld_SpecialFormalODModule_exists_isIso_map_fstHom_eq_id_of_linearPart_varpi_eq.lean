import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hnode₀ : ∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (hnode₁ : ∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)
    (N N' : FormalODModule q (DualNumber k))
    (hN : N.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hN' : N'.map (TrivSqZeroExt.fstHom k k k).toRingHom = X₀.toFormalODModule)
    (hvarpi : MvFormalGroup.linearPart N.varpi = MvFormalGroup.linearPart N'.varpi) :
    ∃ θ : N.Hom N', θ.IsIso ∧ θ.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom = Series.id k := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq.solution
