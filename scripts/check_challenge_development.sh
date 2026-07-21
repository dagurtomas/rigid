#!/usr/bin/env bash

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

lake build Rigid.Challenge Rigid.Development

fixture_dir="$(mktemp -d "${TMPDIR:-/tmp}/rigid-comparator.XXXXXX")"
trap 'rm -rf "$fixture_dir"' EXIT

write_manifest_fixture() {
  local module="$1"
  local target="$2"
  cat >"$target" <<EOF
import $module
import Mathlib.Tactic.Linter.PrivateModule

open Lean Elab Command

private def comparatorNamespace : Name := \`RigidChallenge

private def isComparatorPublicName (env : Environment) (declName : Name) : Bool :=
  let name := declName.toString
  comparatorNamespace.isPrefixOf declName &&
    !isPrivateName declName && !isReservedName env declName &&
    !name.contains "._proof_" && !name.contains ".match_" && !name.contains "._sizeOf_"

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let some output ← IO.getEnv "RIGID_COMPARATOR_MANIFEST" |
    throwError "RIGID_COMPARATOR_MANIFEST is required"
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun entries declName info =>
    if isComparatorPublicName env declName then
      entries.push s!"{declName}|{declarationKind info}"
    else entries
  let entries := entries.qsort fun left right => left < right
  IO.FS.writeFile output (String.intercalate "\n" entries.toList ++ "\n")
EOF
}

challenge_manifest="$fixture_dir/challenge.manifest"
development_manifest="$fixture_dir/development.manifest"
write_manifest_fixture Rigid.Challenge "$fixture_dir/ChallengeManifest.lean"
write_manifest_fixture Rigid.Development "$fixture_dir/DevelopmentManifest.lean"

RIGID_COMPARATOR_MANIFEST="$challenge_manifest" \
  lake env lean "$fixture_dir/ChallengeManifest.lean"
RIGID_COMPARATOR_MANIFEST="$development_manifest" \
  lake env lean "$fixture_dir/DevelopmentManifest.lean"

diff -u "$challenge_manifest" "$development_manifest"

write_type_fixture() {
  local module="$1"
  local target="$2"
  {
    echo "import $module"
    echo
    while IFS='|' read -r name _kind; do
      printf 'set_option pp.all true in\n#check @%s\n\n' "$name"
    done <"$challenge_manifest"
  } >"$target"
}

write_type_fixture Rigid.Challenge "$fixture_dir/ChallengeTypes.lean"
write_type_fixture Rigid.Development "$fixture_dir/DevelopmentTypes.lean"

lake env lean "$fixture_dir/ChallengeTypes.lean" >"$fixture_dir/challenge.raw" 2>&1
lake env lean "$fixture_dir/DevelopmentTypes.lean" >"$fixture_dir/development.raw" 2>&1

normalize() {
  sed -E \
    -e '/^[^:]*\.lean:[0-9]+:[0-9]+: warning:/d' \
    -e 's#^[^:]*\.lean:[0-9]+:[0-9]+: (info: )?##' \
    "$1" >"$2"
}

normalize "$fixture_dir/challenge.raw" "$fixture_dir/challenge.types"
normalize "$fixture_dir/development.raw" "$fixture_dir/development.types"
diff -u "$fixture_dir/challenge.types" "$fixture_dir/development.types"

echo "Challenge and Development expose identical RigidChallenge declarations."
