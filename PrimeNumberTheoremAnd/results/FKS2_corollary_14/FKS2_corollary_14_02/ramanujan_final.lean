import PrimeNumberTheoremAnd.results.FKS2_corollary_14.FKS2_corollary_14_02.Main

namespace FKS2_corollary_14_02

open Real

/--
A compact wrapper around the verified `RamanujanFKS14.ramanujan_final`
theorem, with the threshold written explicitly as `exp 793`.
-/
theorem ramanujan_final :
    ∀ x > exp (793 : ℝ),
      pi x ^ (2 : ℕ) < exp 1 * x / log x * pi (x / exp 1) := by
  intro x hx
  simpa [RamanujanFKS14.exₐ] using RamanujanFKS14.ramanujan_final x hx

end FKS2_corollary_14_02
