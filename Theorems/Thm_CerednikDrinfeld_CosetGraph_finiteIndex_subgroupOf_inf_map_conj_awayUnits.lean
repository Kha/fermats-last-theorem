import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.finiteIndex_subgroupOf_inf_map_conj_awayUnits
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.awayUnits R v ⊓ (CosetGraph.awayUnits R v).map (MulAut.conj s).toMonoidHom).subgroupOf
      (CosetGraph.awayUnits R v)).FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits.solution
