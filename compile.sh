#!/bin/bash

time dune exec -- bin/main.exe compile-to-p benchmarks/$1/task.ml output/$1.scm
