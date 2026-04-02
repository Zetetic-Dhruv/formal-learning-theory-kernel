#!/bin/bash
# Machine-generate the theorem index for the README.
# Groups theorems by directory, shows name, file, line, type, visibility.
# Usage: bash scripts/generate_theorem_index.sh > drafts/theorem_index.md
set -euo pipefail
cd "$(dirname "$0")/.."

echo "## Theorem Index"
echo ""
echo "*Machine-generated from the codebase. $(date -u +%Y-%m-%d).*"
echo ""

# Collect all theorem/lemma declarations from FLT_Proofs/
TMPFILE=$(mktemp)

grep -rn --include="*.lean" -E '^(private )?(theorem|lemma) ' FLT_Proofs/ | while IFS= read -r match; do
  # match format: FLT_Proofs/path/File.lean:123:private theorem foo_bar ...
  file=$(echo "$match" | cut -d: -f1)
  line=$(echo "$match" | cut -d: -f2)
  decl=$(echo "$match" | cut -d: -f3-)

  # Trim leading whitespace
  decl=$(echo "$decl" | sed 's/^[[:space:]]*//')

  # Detect visibility
  vis="public"
  if echo "$decl" | grep -q '^private '; then
    vis="private"
    decl=$(echo "$decl" | sed 's/^private //')
  fi

  # Extract type (theorem or lemma)
  type=$(echo "$decl" | awk '{print $1}')

  # Extract name (second word, strip trailing characters)
  name=$(echo "$decl" | awk '{print $2}')
  # Remove any trailing special chars
  name=$(echo "$name" | sed 's/[^a-zA-Z0-9_'\''.]//g')

  # Short file
  basename=$(basename "$file" .lean)
  dir=$(dirname "$file" | sed 's|^FLT_Proofs/\?||')

  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$dir" "$basename" "$line" "$type" "$vis" "$name"
done | sort -t$'\t' -k1,1 -k2,2 -k3,3n > "$TMPFILE"

# Output grouped by directory
current_dir=""
count=0

while IFS=$'\t' read -r dir basename line type vis name; do
  if [ "$dir" != "$current_dir" ]; then
    if [ -n "$current_dir" ]; then
      echo ""
    fi
    current_dir="$dir"
    case "$dir" in
      ""|".")        echo "### Foundation" ;;
      "Learner")     echo "### Learner" ;;
      "Criterion")   echo "### Criterion" ;;
      "Complexity")  echo "### Complexity" ;;
      "PureMath")    echo "### Pure Mathematics" ;;
      "Theorem")     echo "### Theorems" ;;
      *)             echo "### $dir" ;;
    esac
    echo ""
    echo "| Name | File | Line | Kind | Vis |"
    echo "|------|------|------|------|-----|"
  fi

  echo "| \`$name\` | $basename | $line | $type | $vis |"
  count=$((count + 1))

done < "$TMPFILE"

echo ""
echo "---"
echo ""
echo "**Total: $count theorems/lemmas.**"

rm -f "$TMPFILE"
