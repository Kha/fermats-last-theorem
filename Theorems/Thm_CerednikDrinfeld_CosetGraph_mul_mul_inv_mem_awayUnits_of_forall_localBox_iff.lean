import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_mul_mul_inv_mem_awayUnits_of_forall_localBox_iff

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CerednikDrinfeld CerednikDrinfeld.Omega ValuationSubring QuaternionAlgebra IsDedekindDomain

theorem CerednikDrinfeld.CosetGraph.mul_mul_inv_mem_awayUnits_of_forall_localBox_iff
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (w : (ℍ[ℚ, a, b])ˣ)
    (hw : ∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v → ∀ x : CosetGraph.Loc a b u,
      ((((CosetGraph.toLoc u w)⁻¹ : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) * x *
          ((CosetGraph.toLoc u w : (CosetGraph.Loc a b u)ˣ) : CosetGraph.Loc a b u) ∈ Submodule.localBox R u ↔
        x ∈ Submodule.localBox R u))
    (x : (ℍ[ℚ, a, b])ˣ) (hx : x ∈ CerednikDrinfeld.CosetGraph.awayUnits R v) :
    w * x * w⁻¹ ∈ CerednikDrinfeld.CosetGraph.awayUnits R v := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_mul_mul_inv_mem_awayUnits_of_forall_localBox_iff.solution
