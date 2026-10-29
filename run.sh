#!/usr/bin/env bash
# Model-check the protocol (expected: no error) and the no-READY variant (expected: violation).
set -euo pipefail
cd "$(dirname "$0")"

JAR=tla2tools.jar
if [ ! -f "$JAR" ]; then
  curl -sSL -o "$JAR" https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar
fi

JAVA="${JAVA:-java}"
[ -x /opt/homebrew/opt/openjdk/bin/java ] && [ "$JAVA" = java ] && JAVA=/opt/homebrew/opt/openjdk/bin/java

tlc() { "$JAVA" -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -workers auto -deadlock -config "$1" MC.tla; }

echo "== MC.cfg (ECHO + READY): expected no error =="
tlc MC.cfg | grep -E 'Model checking completed|Error|violated|distinct states found'

echo "== MC_NoReady.cfg (finality at echo quorum): expected Safety violation =="
tlc MC_NoReady.cfg | grep -E 'Error|violated' || true
