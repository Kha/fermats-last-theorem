import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finite_stabilizer_of_finite_stabilizer_dart
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (v : W) (hfin : (𝒯.neighborSet v).Finite) (hne : (𝒯.neighborSet v).Nonempty)
    (hD : ∀ d : 𝒯.Dart, d.fst = v → Finite (stabilizer G d)) :
    Finite (stabilizer G v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.solution
