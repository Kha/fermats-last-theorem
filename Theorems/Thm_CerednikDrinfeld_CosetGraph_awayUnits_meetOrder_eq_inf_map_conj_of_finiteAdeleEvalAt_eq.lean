import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.CosetGraph.awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (q : ℕ) [Fact q.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (s : (ℍ[ℚ, a, b])ˣ) (sf : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hsf : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] u (sf : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) :
    CerednikDrinfeld.CosetGraph.awayUnits (CerednikDrinfeld.meetOrder R sf) v =
      CerednikDrinfeld.CosetGraph.awayUnits R v ⊓
        (CerednikDrinfeld.CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq.solution
