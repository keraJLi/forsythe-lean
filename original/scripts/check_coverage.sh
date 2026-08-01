#!/usr/bin/env bash

set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
project_dir="$(CDPATH= cd -- "${script_dir}/.." && pwd)"
cd "${project_dir}"

production_modules="$({
  find Forsythe -type f -name '*.lean' -print
  printf '%s\n' Forsythe.lean
} | sed 's#/#.#g; s#\.lean$##' | sort -u)"
production_imports="$(sed -n 's/^import \(Forsythe[^ ]*\)$/\1/p' Forsythe.lean | sort -u)"
missing_production="$(printf '%s\n' "${production_modules}" |
  while IFS= read -r module; do
    [[ "${module}" == "Forsythe" ]] && continue
    if ! printf '%s\n' "${production_imports}" | grep -Fqx -- "${module}"; then
      printf '%s\n' "${module}"
    fi
  done)"

if [[ -n "${missing_production}" ]]; then
  printf '%s\n' 'Production modules missing from Forsythe.lean:' >&2
  printf '%s\n' "${missing_production}" >&2
  exit 1
fi

test_modules="$(find ForsytheTest -type f -name '*.lean' -print |
  sed 's#/#.#g; s#\.lean$##' | sort -u)"
test_imports="$(sed -n 's/^import \(ForsytheTest[^ ]*\)$/\1/p' ForsytheTest.lean | sort -u)"
missing_tests="$(printf '%s\n' "${test_modules}" |
  while IFS= read -r module; do
    if ! printf '%s\n' "${test_imports}" | grep -Fqx -- "${module}"; then
      printf '%s\n' "${module}"
    fi
  done)"

if [[ -n "${missing_tests}" ]]; then
  printf '%s\n' 'Regression modules missing from ForsytheTest.lean:' >&2
  printf '%s\n' "${missing_tests}" >&2
  exit 1
fi

if rg --line-number --color never \
    '^[[:space:]]*(axiom|constant|constants|def|abbrev|structure|class|instance|theorem|lemma)\b' \
    Forsythe.lean ForsytheTest.lean; then
  printf '%s\n' 'Aggregators must contain imports and documentation only.' >&2
  exit 1
fi

label_manifest="${project_dir}/scripts/manuscript_labels.txt"
if [[ ! -f "${label_manifest}" ]]; then
  printf 'Missing manuscript-label manifest: %s\n' "${label_manifest}" >&2
  exit 1
fi

invalid_manifest_lines="$(awk '
  !/^(eq|lem):[A-Za-z0-9-]+$/ { print NR ":" $0 }
' "${label_manifest}")"
if [[ -n "${invalid_manifest_lines}" ]]; then
  printf '%s\n' \
    'Invalid manuscript-label manifest lines (expected one eq:/lem: label per line):' >&2
  printf '%s\n' "${invalid_manifest_lines}" >&2
  exit 1
fi

manuscript_labels_all="$(< "${label_manifest}")"
manuscript_labels="$(printf '%s\n' "${manuscript_labels_all}" | sort -u)"

# A label mention in prose is not a blueprint mapping.  Only a backticked
# label in the first column of a Markdown table row counts.
blueprint_labels_all="$(sed -n -E \
  's/^[[:space:]]*\|[[:space:]]*`((eq|lem):[A-Za-z0-9-]+)`[[:space:]]*\|.*/\1/p' \
  Blueprint.md)"
blueprint_labels="$(printf '%s\n' "${blueprint_labels_all}" | sort -u)"

duplicate_manuscript_labels="$(printf '%s\n' "${manuscript_labels_all}" |
  sort | uniq -d)"
if [[ -n "${duplicate_manuscript_labels}" ]]; then
  printf '%s\n' 'Duplicate equation/lemma labels in the manuscript:' >&2
  printf '%s\n' "${duplicate_manuscript_labels}" >&2
  exit 1
fi

duplicate_blueprint_labels="$(printf '%s\n' "${blueprint_labels_all}" |
  sort | uniq -d)"
if [[ -n "${duplicate_blueprint_labels}" ]]; then
  printf '%s\n' 'Duplicate first-column equation/lemma rows in Blueprint.md:' >&2
  printf '%s\n' "${duplicate_blueprint_labels}" >&2
  exit 1
fi

missing_labels="$(printf '%s\n' "${manuscript_labels}" |
  while IFS= read -r label; do
    if ! printf '%s\n' "${blueprint_labels}" | grep -Fqx -- "${label}"; then
      printf '%s\n' "${label}"
    fi
  done)"

if [[ -n "${missing_labels}" ]]; then
  printf '%s\n' 'Manuscript labels missing from Blueprint.md:' >&2
  printf '%s\n' "${missing_labels}" >&2
  exit 1
fi

extra_labels="$(printf '%s\n' "${blueprint_labels}" |
  while IFS= read -r label; do
    if ! printf '%s\n' "${manuscript_labels}" | grep -Fqx -- "${label}"; then
      printf '%s\n' "${label}"
    fi
  done)"

if [[ -n "${extra_labels}" ]]; then
  printf '%s\n' 'First-column Blueprint.md labels absent from the manuscript:' >&2
  printf '%s\n' "${extra_labels}" >&2
  exit 1
fi

# Column two of each equation/lemma row is a machine-checked declaration map:
# every inline-code identifier there must have a corresponding fully qualified
# `#check` in the regression module.  The annotation preserves the spelling in
# the Blueprint even when the Lean check needs additional namespaces.
blueprint_rows_without_declarations="$(awk -F'|' '
  /^[[:space:]]*\|[[:space:]]*`(eq|lem):[A-Za-z0-9-]+`[[:space:]]*\|/ {
    if ($3 !~ /`[^`]+`/) {
      label = $2
      gsub(/^[[:space:]]*`|`[[:space:]]*$/, "", label)
      print label
    }
  }
' Blueprint.md)"

if [[ -n "${blueprint_rows_without_declarations}" ]]; then
  printf '%s\n' 'Blueprint equation/lemma rows without a declaration in column two:' >&2
  printf '%s\n' "${blueprint_rows_without_declarations}" >&2
  exit 1
fi

blueprint_declarations="$(awk -F'|' '
  /^[[:space:]]*\|[[:space:]]*`(eq|lem):[A-Za-z0-9-]+`[[:space:]]*\|/ {
    counterparts = $3
    while (match(counterparts, /`[^`]+`/)) {
      print substr(counterparts, RSTART + 1, RLENGTH - 2)
      counterparts = substr(counterparts, RSTART + RLENGTH)
    }
  }
' Blueprint.md | sort -u)"

declaration_regression='ForsytheTest/BlueprintDeclarations.lean'
if [[ ! -f "${declaration_regression}" ]]; then
  printf 'Missing Blueprint declaration regression: %s\n' \
    "${declaration_regression}" >&2
  exit 1
fi

check_line_count="$(sed -n '/^[[:space:]]*#check[[:space:]]/p' \
  "${declaration_regression}" | wc -l | tr -d '[:space:]')"
annotated_check_line_count="$(sed -n -E \
  's/^[[:space:]]*#check[[:space:]]+([^[:space:]]+)[[:space:]]+--[[:space:]]+blueprint-declaration:[[:space:]]+([^[:space:]]+)[[:space:]]*$/\1|\2/p' \
  "${declaration_regression}" | wc -l | tr -d '[:space:]')"

if [[ "${check_line_count}" != "${annotated_check_line_count}" ]]; then
  printf '%s\n' \
    'Every Blueprint declaration #check must have one same-line blueprint-declaration annotation.' >&2
  exit 1
fi

invalid_declaration_checks="$(sed -n -E \
  's/^[[:space:]]*#check[[:space:]]+([^[:space:]]+)[[:space:]]+--[[:space:]]+blueprint-declaration:[[:space:]]+([^[:space:]]+)[[:space:]]*$/\1|\2/p' \
  "${declaration_regression}" |
  while IFS='|' read -r checked mapped; do
    if [[ "${checked}" != Forsythe.* || "${checked}" != *."${mapped}" ]]; then
      printf '%s -> %s\n' "${mapped}" "${checked}"
    fi
  done)"

if [[ -n "${invalid_declaration_checks}" ]]; then
  printf '%s\n' \
    'Blueprint declaration checks must be fully qualified and end in the mapped name:' >&2
  printf '%s\n' "${invalid_declaration_checks}" >&2
  exit 1
fi

checked_declarations_all="$(sed -n -E \
  's/^[[:space:]]*#check[[:space:]]+[^[:space:]]+[[:space:]]+--[[:space:]]+blueprint-declaration:[[:space:]]+([^[:space:]]+)[[:space:]]*$/\1/p' \
  "${declaration_regression}")"
checked_declarations="$(printf '%s\n' "${checked_declarations_all}" | sort -u)"
duplicate_declaration_checks="$(printf '%s\n' "${checked_declarations_all}" |
  sort | uniq -d)"

if [[ -n "${duplicate_declaration_checks}" ]]; then
  printf '%s\n' 'Duplicate Blueprint declaration regression checks:' >&2
  printf '%s\n' "${duplicate_declaration_checks}" >&2
  exit 1
fi

missing_declaration_checks="$(printf '%s\n' "${blueprint_declarations}" |
  while IFS= read -r declaration; do
    if ! printf '%s\n' "${checked_declarations}" |
        grep -Fqx -- "${declaration}"; then
      printf '%s\n' "${declaration}"
    fi
  done)"

if [[ -n "${missing_declaration_checks}" ]]; then
  printf '%s\n' 'Blueprint declarations missing compile-time #checks:' >&2
  printf '%s\n' "${missing_declaration_checks}" >&2
  exit 1
fi

extra_declaration_checks="$(printf '%s\n' "${checked_declarations}" |
  while IFS= read -r declaration; do
    if ! printf '%s\n' "${blueprint_declarations}" |
        grep -Fqx -- "${declaration}"; then
      printf '%s\n' "${declaration}"
    fi
  done)"

if [[ -n "${extra_declaration_checks}" ]]; then
  printf '%s\n' 'Compile-time #checks absent from the Blueprint equation/lemma map:' >&2
  printf '%s\n' "${extra_declaration_checks}" >&2
  exit 1
fi

printf '%s\n' \
  'Aggregators, manuscript-label rows, and Blueprint declarations are complete.'
