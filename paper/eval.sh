#!/bin/bash

set -e

ghc Abstractions.lhs -e "$1" | ./typeset_math.sh
