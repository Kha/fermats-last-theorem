import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_awayUnits_mono

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.awayUnits_mono
    {a b : ℚ} {R R' : Submodule ℤ ℍ[ℚ, a, b]} (h : R' ≤ R) (v : HeightOneSpectrum (𝓞 ℚ)) :
    CosetGraph.awayUnits R' v ≤ CosetGraph.awayUnits R v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_mono.solution
