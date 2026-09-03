import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_RingHom_bijective_of_surjective_of_smul_eq

theorem RingHom.bijective_of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Function.Bijective g := by p2m_exact_reverting @_root_.P2MW.S_RingHom_bijective_of_surjective_of_smul_eq.solution
