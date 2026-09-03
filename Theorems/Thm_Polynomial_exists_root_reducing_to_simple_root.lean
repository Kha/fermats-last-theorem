import Mathlib.Algebra.Polynomial.Roots
import P2M.Util
import P2M.Sol.S_Polynomial_exists_root_reducing_to_simple_root

theorem Polynomial.exists_root_reducing_to_simple_root {A k : Type*} [CommRing A] [IsDomain A] [CommRing k] [IsDomain k] (red : A →+* k) (s : Multiset A) (b : k) (hb : ((s.map fun a => Polynomial.X - Polynomial.C a).prod.map red).rootMultiplicity b = 1) : ∃ a ∈ s, red a = b ∧ (s.map fun a => Polynomial.X - Polynomial.C a).prod.rootMultiplicity a = 1 ∧ ∀ a' ∈ s, red a' = b → a' = a := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_root_reducing_to_simple_root.solution
