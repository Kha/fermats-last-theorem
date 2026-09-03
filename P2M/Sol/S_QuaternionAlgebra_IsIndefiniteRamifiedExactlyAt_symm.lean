import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
namespace P2MW.S_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm

set_option autoImplicit false

open scoped Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain

theorem solution {a b : ℚ} {q q' : ℕ}
    (h : IsIndefiniteRamifiedExactlyAt a b q q') : IsIndefiniteRamifiedExactlyAt a b q' q :=
  ⟨h.1, fun v => (h.2 v).trans Or.comm⟩
