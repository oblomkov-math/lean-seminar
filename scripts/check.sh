#!/usr/bin/env bash
# Seminar completeness check: is this work really finished?
#
# `lake build` succeeds on a file full of `sorry` — it only emits a warning.
# A clean build is therefore no evidence that a proof is complete. This script is.
#
# Usage, from the top folder of the repository:
#   scripts/check.sh                        # everything under Projects/
#   scripts/check.sh Projects/<YourName>    # your own project
#
# The whole repository is built, but only a `sorry` in a file under the given
# path counts: the exercise files contain `sorry` by design. The trusted-base
# scan looks at the same path.
#
# Exit 0 = everything under the path is complete.

set -uo pipefail

FAIL=0
LOG="$(mktemp)"
SRC="${1:-Projects}"

# A path that does not exist contains nothing, so every check below would pass
# on it. Never report a pass we did not establish.
if [ ! -e "$SRC" ]; then
  echo "FAIL: '$SRC' does not exist. Run this from the top folder of the"
  echo "repository, and check the spelling."
  rm -f "$LOG"
  exit 1
fi

echo "==> lake build"
BUILD=0
lake build 2>&1 | tee "$LOG" || BUILD=$?
if [ "$BUILD" -ne 0 ]; then
  echo "FAIL: build errors."
  FAIL=1
fi

echo
echo "==> checking for incomplete proofs in $SRC"
# Lean reports each `sorry` in the build log like this, with the path relative
# to the top folder:
#
#   warning: Projects/AdaLovelace/Sylow56.lean:40:8: declaration uses `sorry`
#
# Lean v4.34 writes `sorry` in backticks; older versions wrote 'sorry'. Both
# forms match. A module that is already built replays its warnings, so a second
# run still sees them.
SORRY_RE="declaration uses [\`']sorry[\`']"
LINE_RE="^warning: .+\.lean:[0-9]+:[0-9]+: $SORRY_RE"
# $SRC as the log writes paths: no leading `./`, no trailing `/`. "" = all.
SCOPE="${SRC#"$PWD"/}"
while [ "${SCOPE#./}" != "$SCOPE" ]; do SCOPE="${SCOPE#./}"; done
while [ "${SCOPE%/}" != "$SCOPE" ]; do SCOPE="${SCOPE%/}"; done
if [ "$SCOPE" = "." ] || [ "$SCOPE" = "$PWD" ]; then SCOPE=""; fi

if [ "$BUILD" -ne 0 ]; then
  # The build log is the only evidence of `sorry`, and a failed build stops
  # before elaborating everything. Absence of the warning would then prove
  # nothing: do not report a pass that has not been established.
  echo "SKIPPED: the build failed, so the log is incomplete. Fix the build first."
  FAIL=1
else
  # file:line:column of every `sorry`, in build order. Older Lake versions put
  # `./` before the path, and Windows writes `\` in paths.
  ALL="$(grep -E "$LINE_RE" "$LOG" \
    | sed -E 's/^warning: (\.\/)*(.+\.lean:[0-9]+:[0-9]+): .*/\2/' \
    | tr '\\' '/' | awk '!seen[$0]++')"
  # Compared ignoring case: on a Mac, `projects/ada` finds the folder
  # `Projects/Ada`, so it must find that folder's warnings too.
  MINE="$(printf '%s\n' "$ALL" | awk -v s="$SCOPE" '
    BEGIN { s = tolower(s) }
    NF && (s == "" || index(tolower($0), s "/") == 1 || index(tolower($0), s ":") == 1)')"
  # A warning that does not name its file might be about a file under $SRC.
  ODD="$(grep -E "$SORRY_RE" "$LOG" | grep -vE "$LINE_RE")"
  N_ALL="$(printf '%s' "$ALL" | grep -c .)"
  N_MINE="$(printf '%s' "$MINE" | grep -c .)"
  if [ -n "$ODD" ]; then
    echo "FAIL: these 'sorry' warnings do not say which file they are in:"
    printf '%s\n' "$ODD"
    FAIL=1
  elif [ -n "$MINE" ]; then
    echo "FAIL: the following declarations are incomplete:"
    printf '%s\n' "$MINE"
    FAIL=1
  else
    echo "ok: no declaration in $SRC uses 'sorry'"
  fi
  if [ "$N_ALL" -gt "$N_MINE" ]; then
    echo "(not counted: $((N_ALL - N_MINE)) 'sorry' in files outside $SRC)"
  fi
fi

echo
echo "==> checking the trusted base in $SRC"
# `axiom` adds an unproved assumption. `native_decide` trusts the compiler
# rather than only the kernel. Neither belongs in a finished seminar proof.
#
# Comments are blanked before matching — `--` to end of line and nested `/- -/`
# blocks, string literals left intact — so prose naming a banned form does not
# trip the check. A plain `grep` failed on §5 of Seminar/Diagnostics.lean, the
# paragraph that documents the ban. Blanking preserves length and line breaks,
# so the positions printed below are the real ones.
python3 - "$SRC" <<'PY'
import os, pathlib, re, sys

PATTERNS = [
    (re.compile(r'^\s*axiom\s'),   'axiom'),
    (re.compile(r'native_decide'), 'native_decide'),
]


def strip_comments(src: str) -> str:
    """Blank comment text, preserving length and line structure."""
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        c = src[i]
        if depth:                                   # inside /- ... -/, which nests
            if src.startswith('/-', i):
                depth += 1; out.append('  '); i += 2; continue
            if src.startswith('-/', i):
                depth -= 1; out.append('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if in_str:
            out.append(c)
            if c == '\\' and i + 1 < n:             # escape: copy the pair
                out.append(src[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if c == '"':
            in_str = True; out.append(c); i += 1; continue
        if src.startswith('/-', i):
            depth = 1; out.append('  '); i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        out.append(c); i += 1
    return ''.join(out)


root = pathlib.Path(sys.argv[1])
if root.is_file():
    files = [root]
else:
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        # Prune rather than filter: .lake holds all of Mathlib.
        dirnames[:] = [d for d in dirnames if d not in ('.lake', '.git')]
        files += [pathlib.Path(dirpath) / f for f in filenames if f.endswith('.lean')]
    files.sort()

hits = 0
for f in files:
    try:
        text = f.read_text(encoding='utf-8')
    except (OSError, UnicodeDecodeError):
        continue
    for lineno, line in enumerate(strip_comments(text).splitlines(), 1):
        for rx, name in PATTERNS:
            if rx.search(line):
                print(f'{f}:{lineno}: {name}')
                hits += 1

sys.exit(3 if hits else 0)
PY
TB=$?
if [ "$TB" -eq 0 ]; then
  echo "ok: kernel-only trusted base"
elif [ "$TB" -eq 3 ]; then
  echo "FAIL: the forms above enlarge the trusted base beyond the kernel."
  FAIL=1
else
  # An exception, a missing interpreter, a file it could not read: whatever the
  # cause, the scan did not run. Never report a pass we did not establish.
  echo "FAIL: the trusted-base scan could not run (python3 exited $TB)."
  FAIL=1
fi

echo
if [ "$FAIL" -eq 0 ]; then
  echo "PASS: everything in $SRC is complete."
else
  echo "Not complete yet: see FAIL above."
fi
rm -f "$LOG"
exit "$FAIL"
