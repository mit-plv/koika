#!/usr/bin/env bash
## Echo the given command, run it, and time it

TIMEFORMAT=$'  real: %3lR\tuser: %3lU\tsys: %3lS'
echo "$@"
time "$@"
