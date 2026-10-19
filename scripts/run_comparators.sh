#!/usr/bin/env bash
# Run the comparator pairs. A missing pair, a missing tool or a failed check is fatal.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
build=1
only=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --pair) [ "$#" -ge 2 ] || { echo 'Missing pair name' >&2; exit 2; }; only+=("$2"); shift 2 ;;
    --no-build) build=0; shift ;;
    --help) cat <<'USAGE'
Usage: scripts/run_comparators.sh [--pair NAME]... [--no-build]

Runs leanprover/comparator on the pairs under SpherePackingsAudit/ (all six by default), with
the Lean kernel and the nanoda kernel, using separately pinned tools (the revisions are in
.github/workflows/comparator.yml).  Set COMPARATOR_BIN, COMPARATOR_LANDRUN,
COMPARATOR_LEAN4EXPORT and COMPARATOR_NANODA to their executable paths; the defaults are
under ~/tools, as in the workflow.  Unless --no-build is given, the library and the audit
modules are built first (`lake build SpherePackingsAudit`).
Logs are written under .lake/comparator-logs/.
USAGE
      exit 0 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
done
for command_name in lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 1; }
done
: "${COMPARATOR_BIN:=$HOME/tools/comparator/.lake/build/bin/comparator}"
: "${COMPARATOR_LANDRUN:=$HOME/tools/bin/landrun}"
: "${COMPARATOR_LEAN4EXPORT:=$HOME/tools/lean4export/.lake/build/bin/lean4export}"
: "${COMPARATOR_NANODA:=$HOME/tools/nanoda_lib/target/release/nanoda_bin}"
export COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA
for tool_path in "$COMPARATOR_BIN" "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA"; do
  [ -x "$tool_path" ] || { echo "Missing executable: $tool_path" >&2; exit 1; }
done

# Validate every configuration: the six main pairs are present, each permits exactly the three
# standard axioms and enables the nanoda kernel, and its modules exist.
pairs=$(python3 - "$repository_root" "${only[@]+"${only[@]}"}" <<'PY'
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
only = sys.argv[2:]
audit = root / 'SpherePackingsAudit'
required = ['TheoremA', 'TheoremB', 'Prop11', 'Prop11TheoremsAB', 'Theorem61', 'Theorem41']
present = sorted(p.parent.name for p in audit.glob('*/comparator.json'))
missing = set(required) - set(present)
if missing:
    raise SystemExit('Missing required comparator pairs: ' + ', '.join(sorted(missing)))
unknown = set(only) - set(present)
if unknown:
    raise SystemExit('Unknown comparator pairs: ' + ', '.join(sorted(unknown)))
standard = {'propext', 'Classical.choice', 'Quot.sound'}
allowed = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms',
           'definition_names', 'enable_nanoda'}
for name in present:
    path = audit / name / 'comparator.json'
    config = json.loads(path.read_text())
    if set(config) - allowed:
        raise SystemExit(f'{path}: unsupported configuration fields')
    axioms = config.get('permitted_axioms')
    if not isinstance(axioms, list) or len(axioms) != 3 or set(axioms) != standard:
        raise SystemExit(f'{path}: permitted_axioms must be exactly the three standard axioms')
    if config.get('enable_nanoda') is not True:
        raise SystemExit(f'{path}: the nanoda kernel must be enabled')
    if not config.get('theorem_names'):
        raise SystemExit(f'{path}: theorem_names must be a nonempty list')
    for key in ['challenge_module', 'solution_module']:
        module = config.get(key, '')
        if not re.fullmatch(r'SpherePackingsAudit(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module) or \
                not root.joinpath(*module.split('.')).with_suffix('.lean').is_file():
            raise SystemExit(f'{path}: invalid {key}')
print(' '.join(only or present))
PY
)

log_dir="$repository_root/.lake/comparator-logs"
mkdir -p "$log_dir"
if [ "$build" -eq 1 ]; then
  lake build SpherePackingsAudit 2>&1 | tee "$log_dir/audit-build.log"
fi

failed=0
checked=0
for pair in $pairs; do
  printf '\nChecking %s\n' "$pair"
  log="$log_dir/$pair.log"
  if lake env "$COMPARATOR_BIN" "SpherePackingsAudit/$pair/comparator.json" 2>&1 | tee "$log" \
     && grep -Fxq 'Your solution is okay!' "$log" \
     && grep -Fq 'nanoda kernel accepts the solution' "$log" \
     && grep -Fq 'Lean default kernel accepts the solution' "$log"; then
    printf '%s: OK\n' "$pair"
  else
    printf '%s: FAILED\n' "$pair" >&2
    failed=1
  fi
  checked=$((checked + 1))
done
[ "$checked" -ge 1 ] || { echo 'No comparator pair ran' >&2; exit 1; }
[ "$failed" -eq 0 ] || exit 1
printf '\nAll %s comparator pairs passed. Logs: %s\n' "$checked" "$log_dir"
