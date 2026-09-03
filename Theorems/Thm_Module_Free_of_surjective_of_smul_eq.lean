import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_Module_Free_of_surjective_of_smul_eq

theorem Module.Free.of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Module.Free T N := by p2m_exact_reverting @_root_.P2MW.S_Module_Free_of_surjective_of_smul_eq.solution
