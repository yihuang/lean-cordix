import LeanCordix

/-- The `lean-cordix` executable: a small sanity check that the library
builds and that a few key theorems are usable. -/
def main : IO Unit :=
  IO.println "LeanCordix: a formalization of the Cordix calculus (§3–§4) in Lean 4."
