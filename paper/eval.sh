#!/bin/bash

set -e

ghc Abstraction.lhs -e "$1" | ./typeset_math.sh
