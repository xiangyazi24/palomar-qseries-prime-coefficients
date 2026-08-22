#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
challenge="$repository_root/Challenge.lean"
public="$repository_root/PalomarQseriesPrimeCoefficients/Public.lean"
begin_marker='/-! ## BEGIN PUBLIC STATEMENT DEFINITIONS -/'
end_marker='/-! ## END PUBLIC STATEMENT DEFINITIONS -/'

for source in "$challenge" "$public"; do
  if [ "$(grep -Fxc "$begin_marker" "$source")" -ne 1 ]; then
    echo "error: $source must contain exactly one public-definition begin marker" >&2
    exit 1
  fi
  if [ "$(grep -Fxc "$end_marker" "$source")" -ne 1 ]; then
    echo "error: $source must contain exactly one public-definition end marker" >&2
    exit 1
  fi
done

temporary_root=$(mktemp -d)
trap 'rm -rf "$temporary_root"' EXIT

extract_block() {
  local source=$1
  local target=$2
  awk -v begin="$begin_marker" -v end="$end_marker" '
    $0 == begin { copying = 1 }
    copying { print }
    $0 == end { copying = 0 }
  ' "$source" > "$target"
}

extract_block "$challenge" "$temporary_root/challenge.lean"
extract_block "$public" "$temporary_root/public.lean"

if ! diff -u "$temporary_root/challenge.lean" "$temporary_root/public.lean"; then
  echo "error: public statement definitions have drifted" >&2
  exit 1
fi

echo "public statement definition blocks are byte-for-byte identical"
