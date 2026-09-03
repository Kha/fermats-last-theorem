#!/usr/bin/env bash
# Optional second-kernel check with nanoda (https://github.com/ammkrn/nanoda_lib), an independent implementation of the Lean 4 kernel in Rust.
# Linux (bash, git, python3, patch, GNU coreutils, and a Rust toolchain with cargo; cargo fetches crates from the network unless CARGO_FLAGS=--offline
# is given with a vendored source tree). Prerequisite: verification/comparator/run.sh has run (this reuses its lean4export build and wrapper project).
# What it does: writes a second export of the Solution module's environment to a file with the same lean4export (comparator's export list plus the
# Nat/String/Quot built-ins nanoda requires), clones nanoda_lib at the pinned commit, applies the patches in verification/nanoda/patches/
# (instrumentation = a progress line per declaration on stderr; E1, E2, E3 = changes to the order and caching of its definitional-equality search,
# without which a few declarations of this proof occupy unmodified nanoda for many hours each; none of them adds, removes or weakens a typing rule),
# builds it with cargo and runs it with verification/nanoda/nanoda-config.json. Success = exit code 0 and stdout (file nanoda.stdout)
# 'Checked <n> declarations with no errors'.
# Resources: export about 1 h single-threaded, about 90 GB resident and about 40 GB of disk; check about 30 min at 16 threads with all patches,
# about 40 GB resident (VMEM_GB caps address space per process, default 300).
# Knobs (environment): WORK (as for the comparator script), NANODA_SRC (existing checkout to reuse), NANODA_REV, PATCHES (default "instrumentation
# E1-argument-order E2-cache-reset E3-failure-memo"), THREADS (16), VMEM_GB (300), CARGO_FLAGS (e.g. --offline), SKIP_EXPORT=1 (reuse an export).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
HERE=$ROOT/verification/nanoda
WORK=${WORK:-$ROOT/.verify-work}
{ [ -d "$WORK" ] && [ -x "$WORK/bin/lean4export" ] && [ -d "$WORK/wrapper" ]; } || { echo "run verification/comparator/run.sh first (it creates $WORK with bin/lean4export and wrapper/)"; exit 2; }
WORK=$(cd "$WORK" && pwd); W=$WORK/wrapper; EXPBIN=$WORK/bin/lean4export
NANODA_REV=${NANODA_REV:-418320295890faed83a96fd97907b12a3b6728c2}
PATCHES=${PATCHES:-"instrumentation E1-argument-order E2-cache-reset E3-failure-memo"}
THREADS=${THREADS:-16}; VMEM_GB=${VMEM_GB:-300}
log(){ printf '%s %s\n' "$(date -u +%FT%TZ)" "$*"; }
OUT=$WORK/nanoda; mkdir -p "$OUT"

# 1. export the solution's environment to a file (constant list = comparator's export targets for this configuration + nanoda's built-ins)
if [ "${SKIP_EXPORT:-0}" != 1 ] || [ ! -s "$OUT/solution.export" ]; then
  log "exporting Solution with lean4export -> $OUT/solution.export"
  ( cd "$W"; unset LEAN_PATH; export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} LEAN_ABORT_ON_PANIC=1; ulimit -v $((VMEM_GB*1024*1024))
    lake env "$EXPBIN" Solution -- Nat String String.mk Char Quot Quot.mk Quot.lift Quot.ind FLT_for_comparator FLT_mathlib_for_comparator \
      propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor \
      Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce > "$OUT/solution.export" 2> "$OUT/export.err" )
  ( cd "$OUT" && sha256sum solution.export > solution.export.sha256 )
  log "export done: $(cut -c1-16 "$OUT/solution.export.sha256") $(stat -c %s "$OUT/solution.export") bytes"
fi
# 2. nanoda source + patches + build (a patched copy is made once; delete $WORK/src/nanoda-* to redo it)
SRC=${NANODA_SRC:-$WORK/src/nanoda_lib}
if [ ! -d "$SRC" ]; then git clone https://github.com/ammkrn/nanoda_lib "$SRC"; git -C "$SRC" checkout -q "$NANODA_REV"; fi
VAR=$(echo "$PATCHES" | tr -cd 'A-Za-z0-9'); BUILD=$WORK/src/nanoda-$VAR
if [ ! -f "$BUILD/.patched" ]; then
  rm -rf "$BUILD" "$BUILD.tmp"; cp -r "$SRC" "$BUILD.tmp"; rm -rf "$BUILD.tmp/target"
  for p in $PATCHES; do log "applying patches/$p.diff"; ( cd "$BUILD.tmp" && patch -p1 < "$HERE/patches/$p.diff" ); done
  echo "$PATCHES" > "$BUILD.tmp/.patched"; mv "$BUILD.tmp" "$BUILD"
fi
log "building nanoda ($NANODA_REV + $PATCHES)"
( cd "$BUILD" && cargo build --release ${CARGO_FLAGS:-} )
BIN=$BUILD/target/release/nanoda_bin
# 3. run
D=$OUT/run-$VAR; mkdir -p "$D"; cd "$D"
ln -sfn ../solution.export solution.export
python3 - "$HERE/nanoda-config.json" "$THREADS" <<'EOF'
import json, sys; c = json.load(open(sys.argv[1])); c['num_threads'] = int(sys.argv[2]); json.dump(c, open('nanoda-config.json', 'w'), indent=1)
EOF
touch pp.txt   # nanoda 0.4.13 aborts at start-up if pp_output_path does not exist
echo "START $(date -u +%FT%TZ) nanoda=$(git -C "$SRC" rev-parse HEAD 2>/dev/null || echo '?') patches='$PATCHES' bin=$(sha256sum "$BIN" | cut -c1-16) export=$(cut -c1-16 ../solution.export.sha256) threads=$THREADS vmem=${VMEM_GB}GiB" > run.status
log "running nanoda in $D (stdout: nanoda.stdout; per-declaration progress: nanoda.stderr)"
set +e
( ulimit -v $((VMEM_GB*1024*1024)); "$BIN" nanoda-config.json > nanoda.stdout 2> nanoda.stderr ); rc=$?
set -e
echo "END $(date -u +%FT%TZ) rc=$rc stdout='$(head -c 200 nanoda.stdout)' export_after=$(sha256sum ../solution.export | cut -c1-16)" >> run.status
log "nanoda exit code $rc: $(head -c 200 nanoda.stdout)"
exit $rc
