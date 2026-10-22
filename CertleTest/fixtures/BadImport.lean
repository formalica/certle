/-
Regression fixture: broken import must fail loudly.

v4 used to report `replaced 0 proof(s)` with exit code 0 when the header
import could not be loaded (missing `.olean`), because the imported notation
then fails to parse and every theorem loses its proof-body node.  This
fixture imports a module that certainly does not exist; v4 must exit
non-zero and leave the file untouched.
-/
import Certle
import CertleTest.DefinitelyDoesNotExist

theorem wouldOtherwiseBeReplaced (n : Nat) : n + 0 = n := by
  omega
