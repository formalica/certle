#!/usr/bin/env bash
# Regression tests for `CertleExe.lean`.
#
#   CertleTest/run.sh
#
# Covers the two reported issues:
#   1. equation-style declarations whose statement ends in a `do` block
#      (the `mmap_cons` / unexpected-doc-comment-token crash), and
#   2. files whose header imports cannot be loaded (the
#      `Mathlib/Order/Bounds/OrderIso.lean` silent `replaced 0` case),
#      which must now fail loudly instead of exiting 0.
#
# Fixtures are copied into CertleTest/work/ first because v4 rewrites its
# input file in place, and because `lake env lean` only accepts input
# files inside the project root.
set -euo pipefail

cd "$(dirname "$0")/.."
V4="lake env lean --run CertleExe.lean"
V5="lake env lean --run CertleExe.lean"
WORK="CertleTest/work"
FIX="CertleTest/fixtures"
rm -rf "$WORK"
mkdir -p "$WORK"

pass=0
fail=0

ok () { pass=$((pass + 1)); echo "ok   - $1"; }
no () { fail=$((fail + 1)); echo "FAIL - $1"; }

# Copy a fixture and run v4 on the copy.  Sets $status and $log.
run_v4 () {
  local name="$1"
  cp "$FIX/$name" "$WORK/$name"
  set +e
  log="$($V4 "$WORK/$name" 2>&1)"
  status=$?
  set -e
}

# Copy a fixture and run v5 on the copy.  Sets $status and $log.
run_v5 () {
  local name="$1"
  cp "$FIX/$name" "$WORK/$name"
  set +e
  log="$($V5 "$WORK/$name" 2>&1)"
  status=$?
  set -e
}

########################################################################
# Test 1: equation-style declaration ending in a `do` block is replaced
# arm-wise; the file still parses afterwards (issue 1).
########################################################################
run_v4 DoBlockEquation.lean
if [ $status -ne 0 ]; then
  no "DoBlockEquation: v4 exited $status; output: $log"
else
  ok "DoBlockEquation: v4 exited 0"
fi
if echo "$log" | grep -q 'replaced 1 proof(s)'; then
  ok "DoBlockEquation: replaced exactly the 1 non-rfl declaration"
else
  no "DoBlockEquation: expected 'replaced 1 proof(s)', got: $log"
fi
if grep -qE '\| _ => (by )?sorry' "$WORK/DoBlockEquation.lean"; then
  ok "DoBlockEquation: arm body replaced with sorry"
else
  no "DoBlockEquation: arm body was not replaced"
fi
if grep -q 'theorem afterDoBlock (n : Nat) : n = n := rfl' "$WORK/DoBlockEquation.lean"; then
  ok "DoBlockEquation: following rfl declaration survived"
else
  no "DoBlockEquation: following declaration damaged"
fi
if lake env lean "$WORK/DoBlockEquation.lean" >/dev/null 2>&1; then
  ok "DoBlockEquation: rewritten file still compiles"
else
  no "DoBlockEquation: rewritten file does not compile"
fi
# Idempotency: a second run must be a no-op.
before="$(cksum < "$WORK/DoBlockEquation.lean")"
run_v4 DoBlockEquation.lean
after="$(cksum < "$WORK/DoBlockEquation.lean")"
if [ "$before" = "$after" ]; then
  ok "DoBlockEquation: second run is a no-op"
else
  no "DoBlockEquation: second run modified the file again"
fi

########################################################################
# Test 2: OrderIso-shaped file — every non-rfl declaration replaced,
# the rfl one kept (issue 2's positive case).
########################################################################
run_v4 OrderIsoShape.lean
if [ $status -ne 0 ]; then
  no "OrderIsoShape: v4 exited $status; output: $log"
else
  ok "OrderIsoShape: v4 exited 0"
fi
if echo "$log" | grep -q 'replaced 3 proof(s), kept 1'; then
  ok "OrderIsoShape: replaced 3, kept 1 rfl"
else
  no "OrderIsoShape: expected 'replaced 3 proof(s), kept 1', got: $log"
fi
for thm in addCommIff leAddRight mulTwoEq; do
  if grep "theorem $thm" "$WORK/OrderIsoShape.lean" | grep -q 'by sorry'; then
    ok "OrderIsoShape: $thm replaced"
  else
    no "OrderIsoShape: $thm was not replaced"
  fi
done
# the replaced proofs must be gone from the file entirely
if grep -q 'h.symm\|Nat.le_add_right\|omega' "$WORK/OrderIsoShape.lean"; then
  no "OrderIsoShape: original proof bodies still present"
else
  ok "OrderIsoShape: original proof bodies removed"
fi
if grep -q 'theorem keepRfl (n : Nat) : n = n := rfl' "$WORK/OrderIsoShape.lean"; then
  ok "OrderIsoShape: keepRfl kept byte-identical"
else
  no "OrderIsoShape: keepRfl was modified"
fi
if lake env lean "$WORK/OrderIsoShape.lean" >/dev/null 2>&1; then
  ok "OrderIsoShape: rewritten file still compiles"
else
  no "OrderIsoShape: rewritten file does not compile"
fi

########################################################################
# Test 3: broken header import must fail loudly and not touch the file
# (issue 2's negative case: the old v4 printed 'replaced 0' and exited 0).
########################################################################
cp "$FIX/BadImport.lean" "$WORK/BadImport.lean"
before="$(cksum < "$WORK/BadImport.lean")"
set +e
log="$(lake env lean --run CertleExe.lean "$WORK/BadImport.lean" 2>&1)"
status=$?
set -e
after="$(cksum < "$WORK/BadImport.lean")"
if [ $status -ne 0 ]; then
  ok "BadImport: v4 exited $status (non-zero) as required"
else
  no "BadImport: v4 exited 0 on a file with a broken import; output: $log"
fi
if echo "$log" | grep -q 'header/import processing failed'; then
  ok "BadImport: printed the header/import error"
else
  no "BadImport: missing header/import error message; output: $log"
fi
if [ "$before" = "$after" ]; then
  ok "BadImport: file left untouched"
else
  no "BadImport: file was modified despite the failure"
fi

########################################################################
# Test 4: CLI contract — exactly one input file (from the earlier fix).
########################################################################
set +e
log="$(lake env lean --run CertleExe.lean 2>&1)"
status0=$?
log="$(lake env lean --run CertleExe.lean a.lean b.lean 2>&1)"
status2=$?
set -e
if [ $status0 -ne 0 ] && [ $status2 -ne 0 ]; then
  ok "CLI: 0 args and 2 args both rejected with non-zero exit"
else
  no "CLI: arg-count checks broken (0 args: $status0, 2 args: $status2)"
fi

########################################################################
# Test 5: `where` declarations with branches (toCompleteDistribLattice shape)
# Replaced whole with ` := by sorry`.
########################################################################
run_v4 WhereStructure.lean
if [ $status -ne 0 ]; then
  no "WhereStructure: v4 exited $status; output: $log"
else
  ok "WhereStructure: v4 exited 0"
fi
if echo "$log" | grep -q 'replaced 2 proof(s)'; then
  ok "WhereStructure: replaced exactly 2 declarations"
else
  no "WhereStructure: expected 'replaced 2 proof(s)', got: $log"
fi
if grep -qE 'theorem toCompleteDistribLatticeShape \(α : Type\) : MyMinimalAxioms α +:= by sorry' "$WORK/WhereStructure.lean"; then
  ok "WhereStructure: toCompleteDistribLatticeShape whole where replaced with ':= by sorry'"
else
  no "WhereStructure: toCompleteDistribLatticeShape was not replaced correctly"
fi
if grep -qE 'theorem spanSingletonShape \(p q : Prop\) \(h : p ↔ q\) : p ↔ q +:= by sorry' "$WORK/WhereStructure.lean"; then
  ok "WhereStructure: spanSingletonShape whole where replaced with ':= by sorry'"
else
  no "WhereStructure: spanSingletonShape was not replaced correctly"
fi
if grep -qE 'theorem.*where|exact h\.mp|exact h\.mpr' "$WORK/WhereStructure.lean"; then
  no "WhereStructure: original theorem where or branch bodies still present"
else
  ok "WhereStructure: original theorem where and branch bodies removed"
fi
if lake env lean "$WORK/WhereStructure.lean" >/dev/null 2>&1; then
  ok "WhereStructure: rewritten file still compiles"
else
  no "WhereStructure: rewritten file does not compile"
fi
# Idempotency
before="$(cksum < "$WORK/WhereStructure.lean")"
run_v4 WhereStructure.lean
after="$(cksum < "$WORK/WhereStructure.lean")"
if [ "$before" = "$after" ]; then
  ok "WhereStructure: second run is a no-op"
else
  no "WhereStructure: second run modified the file again"
fi

########################################################################
# Test 6: `where` declarations with parent extensions (`__ := ...`)
# Falls back to replacing the whole `where` with ` := by sorry`.
########################################################################
run_v4 WhereParent.lean
if [ $status -ne 0 ]; then
  no "WhereParent: v4 exited $status; output: $log"
else
  ok "WhereParent: v4 exited 0"
fi
if echo "$log" | grep -q 'replaced 1 proof(s)'; then
  ok "WhereParent: replaced exactly 1 declaration"
else
  no "WhereParent: expected 'replaced 1 proof(s)', got: $log"
fi
if grep -qE 'theorem parentStructShape \(α : Type\) : ChildProp α +:= by sorry' "$WORK/WhereParent.lean"; then
  ok "WhereParent: whole where replaced with ':= by sorry'"
else
  no "WhereParent: whole where was not replaced with ':= by sorry'"
fi
if lake env lean "$WORK/WhereParent.lean" >/dev/null 2>&1; then
  ok "WhereParent: rewritten file still compiles"
else
  no "WhereParent: rewritten file does not compile"
fi
# Idempotency
before="$(cksum < "$WORK/WhereParent.lean")"
run_v4 WhereParent.lean
after="$(cksum < "$WORK/WhereParent.lean")"
if [ "$before" = "$after" ]; then
  ok "WhereParent: second run is a no-op"
else
  no "WhereParent: second run modified the file again"
fi

########################################################################
# Test 7: Multi-arm equation declarations
# Replaced with single `| _ => sorry` arm.
########################################################################
run_v4 MultiArmEquation.lean
if [ $status -ne 0 ]; then
  no "MultiArmEquation: v4 exited $status; output: $log"
else
  ok "MultiArmEquation: v4 exited 0"
fi
if echo "$log" | grep -q 'replaced 2 proof(s)'; then
  ok "MultiArmEquation: replaced exactly 2 declarations"
else
  no "MultiArmEquation: expected 'replaced 2 proof(s)', got: $log"
fi
if [ "$(grep -c '| _ => sorry' "$WORK/MultiArmEquation.lean")" -eq 2 ]; then
  ok "MultiArmEquation: both declarations replaced with single '| _ => sorry' arm"
else
  no "MultiArmEquation: expected 2 '| _ => sorry' occurrences"
fi
if lake env lean "$WORK/MultiArmEquation.lean" >/dev/null 2>&1; then
  ok "MultiArmEquation: rewritten file still compiles"
else
  no "MultiArmEquation: rewritten file does not compile"
fi
# Idempotency
before="$(cksum < "$WORK/MultiArmEquation.lean")"
run_v4 MultiArmEquation.lean
after="$(cksum < "$WORK/MultiArmEquation.lean")"
if [ "$before" = "$after" ]; then
  ok "MultiArmEquation: second run is a no-op"
else
  no "MultiArmEquation: second run modified the file again"
fi

########################################################################
# Test 8: Declarations tagged with `@[simps]` (v5 keeps original proof)
########################################################################
run_v5 SimpsLemma.lean
if [ $status -ne 0 ]; then
  no "SimpsLemma: v5 exited $status; output: $log"
else
  ok "SimpsLemma: v5 exited 0"
fi
if echo "$log" | grep -q 'replaced 1 proof(s), kept 0 `rfl` proof(s), kept 1 `simps` proof(s)'; then
  ok "SimpsLemma: replaced 1 non-simps proof, kept 1 simps proof"
else
  no "SimpsLemma: expected 'replaced 1 proof(s)... kept 1 simps proof(s)', got: $log"
fi
if grep -q 'lemma simpsLemmaWithWhere' "$WORK/SimpsLemma.lean" && \
   grep -q 'hp := hp' "$WORK/SimpsLemma.lean" && \
   grep -q 'hq := hq' "$WORK/SimpsLemma.lean"; then
  ok "SimpsLemma: simps lemma kept original proof"
else
  no "SimpsLemma: simps lemma proof was modified"
fi
if grep -qE 'theorem regularTheorem \(n : Nat\) : n \+ 0 = n +:= by sorry' "$WORK/SimpsLemma.lean"; then
  ok "SimpsLemma: regular theorem replaced with ':= by sorry'"
else
  no "SimpsLemma: regular theorem was not replaced with ':= by sorry'"
fi
if lake env lean "$WORK/SimpsLemma.lean" >/dev/null 2>&1; then
  ok "SimpsLemma: rewritten file compiles without simps error"
else
  no "SimpsLemma: rewritten file failed to compile"
fi
# Idempotency
before="$(cksum < "$WORK/SimpsLemma.lean")"
run_v5 SimpsLemma.lean
after="$(cksum < "$WORK/SimpsLemma.lean")"
if [ "$before" = "$after" ]; then
  ok "SimpsLemma: second run is a no-op"
else
  no "SimpsLemma: second run modified the file again"
fi

########################################################################
# Test 9: Quotation patterns with `theorem`/`lemma` (v5 skips quotations)
# Mirrors `Mathlib/Tactic/DeprecateTo.lean` pattern match inside `def`.
########################################################################
run_v5 QuotationPattern.lean
if [ $status -ne 0 ]; then
  no "QuotationPattern: v5 exited $status; output: $log"
else
  ok "QuotationPattern: v5 exited 0"
fi
if echo "$log" | grep -q 'replaced 1 proof(s)'; then
  ok "QuotationPattern: replaced exactly the 1 real theorem"
else
  no "QuotationPattern: expected 'replaced 1 proof(s)', got: $log"
fi
if grep -q 'def renameTheorem' "$WORK/QuotationPattern.lean" && \
   grep -q 'theorem \$id:declId' "$WORK/QuotationPattern.lean" && \
   grep -q 'lemma \$id:declId' "$WORK/QuotationPattern.lean"; then
  ok "QuotationPattern: definition and quotation patterns untouched"
else
  no "QuotationPattern: definition or quotation patterns damaged"
fi
if grep -qE 'theorem regularTheorem \(n : Nat\) : n \+ 0 = n +:= by sorry' "$WORK/QuotationPattern.lean"; then
  ok "QuotationPattern: regular theorem replaced with ':= by sorry'"
else
  no "QuotationPattern: regular theorem was not replaced with ':= by sorry'"
fi
if lake env lean "$WORK/QuotationPattern.lean" >/dev/null 2>&1; then
  ok "QuotationPattern: rewritten file still compiles"
else
  no "QuotationPattern: rewritten file failed to compile"
fi
# Idempotency
before="$(cksum < "$WORK/QuotationPattern.lean")"
run_v5 QuotationPattern.lean
after="$(cksum < "$WORK/QuotationPattern.lean")"
if [ "$before" = "$after" ]; then
  ok "QuotationPattern: second run is a no-op"
else
  no "QuotationPattern: second run modified the file again"
fi

########################################################################
echo
echo "passed $pass, failed $fail"
[ $fail -eq 0 ]
