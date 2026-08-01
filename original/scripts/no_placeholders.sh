#!/usr/bin/env bash

set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
project_dir="$(CDPATH= cd -- "${script_dir}/.." && pwd)"
cd "${project_dir}"

# Keep this deliberately conservative: proof-placeholder words are also forbidden
# in production comments. Tests, the blueprint, and vendored Lake packages are out
# of scope.
placeholder_pattern='\b(sorry|admit|axiom|sorryAx)\b'

if rg \
  --line-number \
  --color never \
  --glob '*.lean' \
  "${placeholder_pattern}" \
  Forsythe.lean Forsythe
then
  printf '%s\n' 'Production Lean sources contain a forbidden proof placeholder.' >&2
  exit 1
fi

# `constant`/`constants` commands also introduce value-less declarations and
# are therefore project axioms even though they do not contain the word
# `axiom`.  Ordinary prose uses “constant” heavily, so check command starts.
if rg \
  --line-number \
  --color never \
  --glob '*.lean' \
  '^[[:space:]]*(constant|constants)[[:space:]]+[[:alnum:]_.]+[[:space:]]*([({:]|$)' \
  Forsythe.lean Forsythe
then
  printf '%s\n' 'Production Lean sources contain a project-defined constant axiom.' >&2
  exit 1
fi

printf '%s\n' 'Production Lean sources contain no forbidden proof placeholders.'
