import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.act_pow_mem_span_of_isODHom_of_hasKernelOfDegree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hp : IsNilpotent ((p : ℕ) : B))
    (X Y : FormalODModule p B) (ρ : Series B) (hρ : FormalODModule.IsODHom X Y ρ)
    (h : ℕ) (hdeg : FormalODModule.HasKernelOfDegree ρ (p ^ h)) :
    ∀ i : Fin 2, X.act ((p : Zp2 p) ^ h) i ∈ Ideal.span (Set.range ρ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_act_pow_mem_span_of_isODHom_of_hasKernelOfDegree.solution
